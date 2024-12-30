function fact(n: nat): nat
    requires n >= 1
    decreases n
{
    if n == 1 then 1
    else fact(n-1) * n
}


method ComputeFact(n : nat) returns (res : nat)
  requires n > 0
  ensures res == fact(n)
 {
  res := 1;
  var i := 2;
  while (i <= n)
    invariant res == fact(i - 1) && 1 <= i <= n + 1
  {
    res := res * i;
    i := i + 1;
  }
 }