method plusTwo(x: int) returns (y: int)
    requires x == -1

    ensures 0 <= y
    ensures 0 <= x ==> y == x
    ensures x < 0 ==> y == -x
{
    y := x + 2;
}

/*
DONT exist, it is illiegal
method plusOne(x: int) returns (y: int)
    requires x == 0

    ensures 0 <= y;
    ensures 0 <= x ==> y == x;
    ensures x < 0 ==> y == -x;
{
    y := x + 1;
}
*/