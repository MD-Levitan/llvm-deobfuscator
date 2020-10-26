from binaryninja import *
from operator import *
from pprint import *
from itertools import chain
from .util import *


class CFGLink(object):
    def __init__(self, arch, block, true_block, false_block=None, def_il=None):
        """ Create a link from a block to its real successors

        Args:
            arch: architure
            block (BasicBlock): block to start from
            true_block (BasicBlock): The target block of an unconditional jump,
                or the true branch of a conditional jump
            false_block (BasicBlock): The false branch of a conditional jump
            def_il (MediumLevelILInstruction): The instruction that was used
                to discover this link. This will be a definition of the state
                variable
        """
        self.arch = arch
        self.il = def_il  # The definition il we used to find this link
        self.block = block

        # Resolve the true/false blocks
        self.true_block = true_block.outgoing_edges[0].target
        self.false_block = false_block
        if self.false_block is not None:
            self.false_block = self.false_block.outgoing_edges[0].target

    @property
    def is_uncond(self):
        return self.false_block is None

    @property
    def is_cond(self):
        return not self.is_uncond

    def gen_asm(self, bv: BinaryView, base_addr):
        """ Generates a patch to repair this link

        For an unconditional jump, this will generate
            jmp next_block

        For a conditional jump, this will generate
            jcc true_block
            jmp false_block
        where cc is the condition used in the original CMOVcc in the flattening logic

        Args:
            bv (BinaryView)
            base_addr (int): The address where these instructions will be placed.
                This is necessary to calculate relative addresses

        Returns:
            str: The assembled patch opcodes
        """
        # It's assumed that base_addr is the start of free space
        # at the end of a newly recovered block
        def rel(addr):
            return hex(addr - base_addr).rstrip('L')
            
        # Unconditional jmp
        # TODO: add jump for differernt arch
        if self.is_uncond:
            next_addr = self.true_block.start
            print(
                '[+] Patching from {:x} to {:x}'.format(base_addr, next_addr))
            return safe_asm(bv, 'jmp {}'.format(rel(next_addr)), self.arch)
            
        # Branch based on original cmovcc
        else:
            assert self.il is not None
            true_addr = self.true_block.start
            false_addr = self.false_block.start
            print('[+] Patching from {:x} to T: {:x} F: {:x}'.format(base_addr,
                                                                     true_addr,
                                                                     false_addr))

            # Find the cmovcc by looking at the def il's incoming edges
            # Both parent blocks are part of the same cmov
            il_bb = next(bb for bb in self.il.function if bb.start <=
                         self.il.instr_index < bb.end)
            cmov_addr = il_bb.incoming_edges[0].source[-1].address
            cmov = bv.get_disassembly(cmov_addr).split(' ')[0]

            # It was actually painful to write this
            jmp_instr = cmov.replace('cmov', 'j')

            # Generate the branch instructions
            asm = safe_asm(bv, '{} {}'.format(jmp_instr, rel(true_addr)), self.arch)
            base_addr += len(asm)
            asm += safe_asm(bv, 'jmp {}'.format(rel(false_addr)), self.arch)

            return asm

    def __repr__(self):
        if self.is_uncond:
            return '<U Link: {} => {}>'.format(self.block,
                                               self.true_block)
        else:
            return '<C Link: {} => T: {}, F: {}>'.format(self.block,
                                                         self.true_block,
                                                         self.false_block)


COMPARE_OPERATIONS = (MediumLevelILOperation.MLIL_CMP_E, MediumLevelILOperation.MLIL_CMP_NE, MediumLevelILOperation.MLIL_CMP_SGE,
                      MediumLevelILOperation.MLIL_CMP_SGT, MediumLevelILOperation.MLIL_CMP_SLE, MediumLevelILOperation.MLIL_CMP_SLT,
                      MediumLevelILOperation.MLIL_CMP_UGE, MediumLevelILOperation.MLIL_CMP_UGT, MediumLevelILOperation.MLIL_CMP_ULE,
                      MediumLevelILOperation.MLIL_CMP_ULT)


def compute_backbone_map(bv: BinaryView, mlil: MediumLevelILFunction, state_var: Variable):
    """ Recover the map of state values to backbone blocks

    This will generate a map of
    {
        state1 => BasicBlock1,
        state2 => BasicBlock2,
        ...
    }

    Where BasicBlock1 is the block in the backbone that will dispatch to
    an original block if the state is currently equal to state1

    Args:
        bv (BinaryView)
        mlil (MediumLevelILFunction): The MLIL for the function to be deflattened
        state_var (Variable): The state variable in the MLIL

    Returns:
        dict: map of {state value => backbone block}
    """
    backbone = {}

    # The state variable itself isn't always the one referenced in the
    # backbone blocks, they may instead use another pointer to it.
    # Find the variable that all subdispatchers use in comparisons
    var = state_var
    uses = mlil.get_var_uses(var)

    print_debug(uses, "USES")

    # The variable with >2 uses is probable the one in the backbone blocks
    while len(uses) <= 2:
        var = mlil[uses[-1]].dest
        uses = mlil.get_var_uses(var)

        print_debug(uses, "LOCAL USES")

    uses += mlil.get_var_definitions(var)

    print_debug(uses, "USES2")

    # Gather the blocks where this variable is used
    blks = (b for il in uses for b in mlil.basic_blocks if b.start <=
            il.instr_index < b.end)

    print_debug(blks, "Blocks")

    # In each of these blocks, find the value of the state
    for bb in blks:

        # Find the comparison
        # print()
        # print()
        # print_block_debug(bb, "Full Block")
        # print_debug(bb[-1], "Block")
        # print_debug(bb[-1].operation, "Block type")

        # Check only IL with condition
        if bb[-1].operation != MediumLevelILOperation.MLIL_IF:
            continue

        # To avoid situations when condtition is constant = {"true", "false"}.
        # TODO: But have to add special block to process it.
        # TODO: Also add situations when MediumLevelILOperation.MLIL_FCMP_*.
        if bb[-1].condition.operation in COMPARE_OPERATIONS:
            # Find state of this condition. We should separate two situations:
            # 1. Right value is some value and we should found in mlil.
            # 2. Right value is constant value.
            right_value = bb[-1].condition.right

            if right_value.operation == MediumLevelILOperation.MLIL_VAR:
                cond_var = right_value.vars_read[0]
                cmp_il = mlil[mlil.get_var_definitions(cond_var)[0]]
                # TODO: Process sutiation when it is more copmlicated llvm-obfuscation
                # TODO: and `cmp_il` - it's another condition.
                state = cmp_il.src.constant
            elif right_value.operation == MediumLevelILOperation.MLIL_CONST or right_value.operation == MediumLevelILOperation.MLIL_CONST_PTR:
                state = right_value.constant
            # TODO: Check probabilty of another situations
            else:
                continue

        # Process situation when condition is bool value
        # Example:
        #       34 @ 00401166  rax_4 = var_20_1
        #       35 @ 00401169  temp2_1 = rax_4
        #       36 @ 00401169  rax_5 = rax_4 - 0xf675d982
        #       37 @ 00401169  cond:2_1 = temp2_1 == 0xf675d982
        #       38 @ 0040116e  var_2c_1 = rax_5
        #       39 @ 00401171  if (cond:2_1) then 40 @ 0x40128f else 42 @ 0x401177
        elif bb[-1].condition.operation in (MediumLevelILOperation.MLIL_VAR, ):
            cond_var = bb[-1].condition.src
            cmp_il = mlil[mlil.get_var_definitions(cond_var)[0]]

            if cmp_il.src.operation == MediumLevelILOperation.MLIL_CONST:
                state = cmp_il.src.constant
            elif cmp_il.src.operation in COMPARE_OPERATIONS:
                state = cmp_il.src.right.constant
            else:
                print("[!] cannot process situation")
                print(bb[-1])
                continue
        else:
            continue

        # Pull out the state value
        address = bv.get_basic_blocks_at(bb[0].address)[0]

        print(
            "[+] Add new backbone: addr - {}, state - {}/{}".format(address, state, hex(state)))
        backbone[state] = address

    return backbone


def compute_original_blocks(bv: BinaryView, mlil: MediumLevelILFunction, state_var: Variable):
    """ Gathers all MLIL instructions that (re)define the state variable
    Args:
        bv (BinaryView)
        mlil (MediumLevelILFunction): The MLIL for the function to be deflattened
        state_var (Variable): The state variable in the MLIL

    Returns:
        tuple: All MediumLevelILInstructions in mlil that update state_var
    """
    original = mlil.get_var_definitions(state_var)
    return original
    # return itemgetter(*original)(mlil)


def resolve_cfg_link(bv: BinaryView, mlil: MediumLevelILFunction, il: MediumLevelILInstruction, backbone: dict):
    """ Resolves the true successors of a block

    When there is only one successor, the state variable is set to a constant,
    so we simply look this new state in the backbone map

    When there are 2 successors, we rely on SSA form to decide which successor
    state is the true/false branch. Of the two possible values that the next state
    may be, the earlier version (default value) corresponds to the false branch

    Args:
        bv (BinaryView)
        mlil (MediumLevelILFunction): The MLIL for the function to be deflattened
        il (MediumLevelILInstruction): An instruction in one of the original blocks
            that updates the state variable
        backbone (dict): map of {state value => backbone block}

    Returns:
        CFGLink: a link with the resolved successors for the block il was contained in
    """
    # il refers to a definition of the state_var
    bb = bv.get_basic_blocks_at(il.address)[0]

    # Unconditional jumps will set the state to a constant
    if il.src.operation == MediumLevelILOperation.MLIL_CONST or il.src.operation == MediumLevelILOperation.MLIL_CONST_PTR:
        block = backbone.get(il.src.constant, None)
        if block is None:
            print("Failed to add value: {}/{}".format(il.src.constant,
                                                      hex(il.src.constant)))
        else:
            return CFGLink(mlil.arch, bb, block, def_il=il)

    # Conditional jumps choose between two values
    else:
        # Go into SSA to figure out which state is the false branch
        # Get the phi for the state variable at this point
        phi = get_ssa_def(mlil, il.ssa_form.src.src)
        assert phi.operation == MediumLevelILOperation.MLIL_VAR_PHI

        # The cmov (select) will only ever replace the default value (false)
        # with another if the condition passes (true)
        # So all we need to do is take the earliest version of the SSA var
        # as the false state
        # v = sorted(phi.src, key=lambda var: var.version)
        # print(v)

        f_def, t_def = sorted(phi.src, key=lambda var: var.version)

        # There will always be one possible value here
        false_state = get_ssa_def(mlil, f_def).src.possible_values.value
        true_state = get_ssa_def(mlil, t_def).src.possible_values.value

        return CFGLink(mlil.arch, bb, backbone[true_state], backbone[false_state], il)
    return None


def clean_block(bv: BinaryView, mlil: MediumLevelILFunction, link: CFGLink):
    """ Return the data for a block with all unnecessary instructions removed

    Args:
        bv (BinaryView)
        mlil (MediumLevelILFunction): The MLIL for the function to be deflattened
        link (CFGLink): a link with the resolved successors for a block

    Returns:
        str: A copy of the block link is based on with all dead instructions removed
    """

    # Helper for resolving new addresses for relative calls
    def _fix_call(bv, addr, newaddr, arch):
        print("Address: {} -- {}".format(hex(addr), hex(newaddr)))
        tgt = llil_at(bv, addr).dest.constant
        print("Address updated: {} -- {}".format(hex(tgt), hex(newaddr)))

        # reladdr = hex(tgt - newaddr).rstrip('L')
        reladdr = hex(tgt).rstrip('L')
        return safe_asm(bv, 'bl {}'.format(reladdr), arch=arch)
        # return safe_asm(bv, 'call {}'.format(reladdr))

    # The terminator gets replaced anyway
    block = link.block
    old_len = block.length
    nop_addrs = {block.disassembly_text[-1].address}
    print(block.disassembly_text)

    # Gather all addresses related to the state variable
    if link.il is not None:
        gather_defs(link.il.ssa_form, nop_addrs)

    print("[+] Gather addresses")
    print(" ".join(map(lambda x: hex(x), nop_addrs)))

    # Rebuild the block, skipping the bad instrs
    addr = block.start
    data = b''
    arch = mlil.arch
    

    while addr < block.end:
        # How much data to read
        ilen = bv.get_instruction_length(addr, arch=arch)
        print("Iter: {} - {} - {}".format(hex(addr), hex(block.end), ilen))
        print("Assem: {}".format(bv.get_disassembly(addr, arch=arch)))

        assert ilen != 0

        # Only process this instruction if we haven't blacklisted it
        if addr not in nop_addrs:
            # Calls need to be handled separately to fix relative addressing
            # TODO: add fix_call
            # if is_call(bv, addr):
            #     data += _fix_call(bv, addr, block.start + len(data))
            # else:

            data += bv.read(addr, ilen)

        # Next instruction
        addr += ilen
    return data, block.start + len(data), old_len


def gather_full_backbone(backbone_map: dict):
    """ Collect all blocks that are part of the backbone

    Args:
        backbone_map (dict): map of {state value => backbone block}

    Returns:
        set: All BasicBlocks involved in any form in the backbone
    """
    # Get the immediately known blocks from the map
    backbone_blocks = list(backbone_map.values())
    backbone_blocks += [bb.outgoing_edges[1].target for bb in backbone_blocks]

    # Some of these blocks might be part of a chain of unconditional jumps back to the top of the backbone
    # Find the rest of the blocks in the chain and add them to be removed
    for bb in backbone_blocks:
        blk = bb
        while len(blk.outgoing_edges) == 1:
            if blk not in backbone_blocks:
                backbone_blocks.append(blk)
            blk = blk.outgoing_edges[0].target
    return set(backbone_blocks)


def deflatten_cfg(bv: BinaryView, addr: int):
    """ Reverses the control flow flattening pass from OLLVM

    Args:
        bv (BinaryView)
        addr (int): Selected address in the view. This should be an
            instruction where the state variable is updated
    """
    print(bv.arch)

    func = get_func_containing(bv, addr)
    mlil = func.mlil

    # TODO: make options to choose default algorithim or with super_value.
    # Example:
    #   39 @ 0000e2c8  r0_4 = r8_1
    #   40 @ 0000e2cc  if (r0_4 s> r3) then 41 @ 0xe350 else 42 @ 0xe2d0
    # All conditions check r0_4 but sets r8_1 value. That's way during
    # computation of backbones we should use r0_4 - `state_var`, and
    # during computation of original block r8_4 - `super_state_var`.

    state_var = func.get_low_level_il_at(addr).medium_level_il.dest
    # super_state_var = func.get_low_level_il_at(addr).medium_level_il.src.src

    # compute all usages of the state_var
    backbone = compute_backbone_map(bv, mlil, state_var)
    print('[+] Computed backbone')
    pprint(backbone)

    # compute all the defs of the state_var in the original basic blocks
    original = compute_original_blocks(bv, mlil, state_var)
    print('[+] Usages of the state variable in original basic blocks')
    pprint(original)

    # at this point we have all the information to reconstruct the CFG
    CFG = list(filter(lambda x: x is not None, [resolve_cfg_link(
        bv, mlil, il, backbone) for il in original]))
    print('[+] Computed original CFG')
    pprint(CFG)

    # patch in all the changes
    print('[+] Patching all discovered links')
    for link in CFG:
        print('[+] Patching link: {}'.format(link))
        # Clean out instructions we don't need to make space
        blockdata, cave_addr, orig_len = clean_block(bv, mlil, link)

        # Add the new instructions and patch, nop the rest of the block
        blockdata += link.gen_asm(bv, cave_addr)

        blockdata = blockdata.ljust(orig_len, safe_asm(bv, 'nop', arch=mlil.arch))
        
        # nop_instr = safe_asm(bv, 'nop', arch=mlil.arch)
        # blockdata = blockdata + nop_instr * \
        #     ((len(blockdata) - orig_len) // len(nop_instr))

        print("[+]Add block: {}".format(len(blockdata)))

        bv.write(link.block.start, blockdata)

    # Do some final cleanup
    print('[+] NOPing backbone')
    nop = safe_asm(bv, 'nop', mlil.arch)
    for bb in gather_full_backbone(backbone):
        print('[+] NOPing block: {}'.format(bb))
        bv.write(bb.start, nop * bb.length)


"""
Example CFG:
[<C Link: <block: x86_64@0x4006e7-0x400700> => T: <block: x86_64@0x400700-0x400720>, F: <block: x86_64@0x400735-0x400741>>,
 <U Link: <block: x86_64@0x4006d4-0x4006e7> => <block: x86_64@0x4006e7-0x400700>>,
 <U Link: <block: x86_64@0x400700-0x400720> => <block: x86_64@0x400720-0x400735>>,
 <U Link: <block: x86_64@0x4006b4-0x4006d4> => <block: x86_64@0x400741-0x400749>>,
 <U Link: <block: x86_64@0x400735-0x400741> => <block: x86_64@0x400741-0x400749>>,
 <C Link: <block: x86_64@0x400699-0x4006b4> => T: <block: x86_64@0x4006b4-0x4006d4>, F: <block: x86_64@0x4006d4-0x4006e7>>,
 <U Link: <block: x86_64@0x400720-0x400735> => <block: x86_64@0x4006e7-0x400700>>]
"""
