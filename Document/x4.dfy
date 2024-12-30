function max(a: int, b: int) : int 
{
    if a > b then a else b
}

method Test(){
    assert max(22, 44) == 44;
    assert max(44, 22) == 44;
    assert 34 < max(22, 44);

}