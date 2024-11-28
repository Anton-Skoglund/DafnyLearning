
method hold(n: nat) returns (b: int)
{
    var i: int := 0;
    while (i < n)
        invariant 0 <= i <= n;
        decreases n - i; // if i pass n never end
    {
        i := i + 1; // change to + n + 1 then never ends
    }
    b := i;
    assert i == n;
}

// Dont work

/*
method hold(n: nat) returns (b: int)
{
    var i: int := 0;
    while (i != n)
    decreases n - i; // if i pass n never end
    {
        i := i + 1; // change to + n + 1 then never ends
    }
    b := i;
}
*/