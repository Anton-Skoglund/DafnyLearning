// x8
method invariantTest(n: nat){
    var i := 0;
    while (i != n)
        invariant 0 <= i <= n
    {
        i := i + 1;
    }
    assert n == i;
}

// x7
/* 
No becuase it might keep going or adding 2 it dont know
method invariantTest(n: nat){
    var i := 0;
    while (i < n)
        invariant 0 <= i <= n + 2;
    {
        i := i + 1;
    }
    assert n == i;
}
*/

/* START METHOD
method invariantTest(n: nat){
    var i := 0;
    while (i < n)
        invariant 0 <= i <= n;
    {
        i := i + 1;
    }
    assert n == i;
}
*/