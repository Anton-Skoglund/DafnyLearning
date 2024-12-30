



function sorted(a: array<int>): bool
    reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}


method InsertionSort(a: array<int>)
    modifies a

    requires a.Length > 0
    ensures sorted(a)
{   
    if(a.Length == 1){
        return;
    }

    var i: int := 1;


    while(i < a.Length)
        invariant 1 <= i <= a.Length
        invariant sorted(a[..(i-1)])

        decreases a.Length - i
    {
        var j: int := i;
        while(j > 0 && a[j-1] > a[j])
        invariant 0 <= j <= a.Length
        {
            var temp: int := a[j];
            a[j] := a[j-1];
            a[j-1] := temp;
            j := j - 1;
        }
        i := i + 1;
    }
}



