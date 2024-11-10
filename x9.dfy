function fib(n: nat): nat
{
    if n == 0 then 0 else
    if n == 1 then 1 else
    fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
    requires n > 0
    ensures b == fib(n);
{
    var i := 1;
    b := 1;
    var c := b;
    while (i < n)
        invariant 0 < i <= n;
        invariant b == fib(i);
        invariant c == fib(i + 1);
    {
        b, c := c, c + b;
        i := i + 1;
    }
}