method Max(a: array<int>) returns (index: int)
    // array is not null and lenght greater then zero
    requires a != null && a.Length > 0
    // the return is between 0 and lenght and for all i in the array the index we retur will have a greater or equal value to all
    ensures 0 <= index < a.Length && forall i :: 0 <= i < a.Length ==> a[index] >= a[i]
{
    var maxIndex := 0;
    var i := 1;
    while i < a.Length
        invariant 0 <= maxIndex < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> a[maxIndex] >= a[j]
    {
        if a[i] > a[maxIndex] {
            maxIndex := i;
        }
        i := i + 1;
    }
    index := maxIndex;
}
