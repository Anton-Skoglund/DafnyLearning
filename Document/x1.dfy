include "x0.dfy"

method MaxTest(){
    var a: int := 10;
    var b: int := 20;
    var max := Max(a, b);
    assert max != a + b;
    assert max < a + b;
    assert max != a || max == a;
    
    var a2: int := 0;
    var b2: int := 20;
    var max2 := Max(a2, b2);
    /* 
    they do not hold for these values
    assert max2 != a2 + b2;
    assert max2 < a2 + b2;
    assert max2 != a2 || max == a2;
    */
}