method Max(x: int, y: int) returns (max: int)
    ensures max == x || max == y
{
    if(x > y){
        return x;
    }

    return y;
}

/*
method Max(x: int, y: int) returns (max: int)
{
    if(x > y){
        max := x;
    }
    max := y;
}
*/

/*
method Max(x: int, y: int) returns (max: int)
{
    if(x > y){
        return x;
    }
    max := y;
}
*/

/*
method Max(x: int, y: int) returns (max: int)
{
    if(x > y){
        max := x;
    }else{
        max := y;
    }
}
*/