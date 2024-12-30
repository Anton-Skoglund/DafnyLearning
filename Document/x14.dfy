
// works without the null check ????
// think the static wont complin but you get runtime error

function sorted(a: array<int>): bool
    reads a
{
    a != null && forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k]
}


method BinarySearch(a: array<int>, key: int) returns (index: int)
    requires sorted(a)
    ensures 0 <= index ==> index < a.Length && a[index] == key
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
    var low, high := 0, a.Length;
    while (low < high)
        invariant 0 <= low <= high <= a.Length;
        invariant forall i :: 0 <= i < a.Length && !(low <= i < high)
                          ==> a[i] != key
    {
        var mid := (low + high) / 2;
        if (a[mid] < key) {
            low := mid + 1;
        } else if (key < a[mid]) {
            high := mid;
        } else {
            index := mid;
        return;
        }
    }
    index := -1;
}