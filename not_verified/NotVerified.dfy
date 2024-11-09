method Multiply(a: int, b: int) returns (result: int)
    ensures result == a + b  // Postcondition: result should be the sum of a and b, which is incorrect
{
    result := a * b;  // Correct multiplication
}
