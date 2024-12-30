function abs(x: int): int
{
    if x > 0 then x else -x
}


method Abs(x: int) returns (y: int)
    ensures y == abs(x)
{
    if (x < 0) { y := -x; }
    else { y := x; }
}