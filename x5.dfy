function method max(a: int, b: int) : int 
{
    if a > b then a else b
}

method Test(){
    var maxVar: int := max(22, 44);
    assert maxVar == 44;
    assert 34 < maxVar;
}