function sorted(a: array<int>): bool
    requires a != null
    reads a
{
    forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k]
}