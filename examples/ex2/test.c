unsigned int call1(unsigned int a)
{
  a += 1;

  return a;
}

unsigned int call2(unsigned int a)
{
  a &= 0xFF;
  a -= 0x20;

  return a;
}

unsigned int target_function(unsigned int n)
{
  unsigned int mod = n % 4;
  unsigned int result = 0;

  if (mod == 0) result = (n | 0xBAAAD0BF) * (2 ^ n);

  else if (mod == 1) result = (n & 0xBAAAD0BF) * (3 + call1(n));

  else if (mod == 2) result = (n ^ 0xBAAAD0BF) * (4 | call2(n));

  else result = (n + 0xBAAAD0BF) * (5 & n);

  return result;
}

int main()
{
	target_function(123);
}

