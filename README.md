# DafnyLearning
A introduciton to dafny exercie

## Shout out user: bor0
Insparation - https://github.com/bor0/dafny-tutorial

Solution to - https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml220.pdf

Run online - https://tio.run/#dafny


## Dont know if you can run
- All the compile files are ignored and i dont know if they are need or generated on the spot❤️


## Notes form text
- I cnat spell (writen for my eyese)
You write in annotaions that can be proven correct or false, it is easier than writing correct code.


### Method-ish section
- Cant appera in expersion, no recursion
- Uppser case letter in start
``` dafny
    forall k: int :: 0 <= k < a.Length ==> 0 < a[k]

    x := 1 (x = 1 in most other programing)
```

returns at the end so you can set r := 1 or return 1, if r := 1 it will return the value that r has in the end.

### Pre - Post
You can have pre and post conditions

Put requires before ensures (not need often but looks good)
``` dafny
    // pre 
    requires pre < 2
    // post
    ensuers return > 2

    // chaning
    ensures 1 < x < 3
    // not 
    ensures 1 < x > 2
```

- Typing check is a kind of preconditon


### Assert

``` dafny
    assert 2 < 3
```

### local var
Use it to look at return values because you cant put the function in the test becuase it might change, which makes it hard to change everywhere?
``` dafny
    var x: int := 5; // optional type
    // multli declariton
    var x, y, z: bool := 1, 2, true; // z is bool x, y get intrepreted as int
```

### Tests
Test dont run the function only look at post condtion, which you can test that function to know if they really hold, so to test you need to write good post conditions.

I think it does the same with pre conditions like check them before.


### Functions
They are like math functions
One return value, no write to memory
- You can hav recursion
``` dafny
function fib(n: nat): nat
{
    if n == 0 then 0 else
    if n == 1 then 1 else
    fib(n - 1) + fib(n - 2)
}
```
- lower case letter for function
- Only one expresion per function
- There limitations to no wirte to memory and not have complex returns makes them suable to test without pre conditions or make a variable for them.
- YOU can not write var y := function(x);
- Function are tools to verify code not to compile
``` dafny
function abs(x: int): int
{
    if x < 0 then -x else x
}
```

### Funciton methods

``` dafny
function abs(x: int): int
{
    if x < 0 then -x else x
}
```

### Loops / loops invariants
``` dafny
var i := 0;
while (i < n)
{
    i := i + 1;
}
```

- loops are hard becuase we cant say before how many times it will run, but invariant can help
#### invariant
``` dafny
var i := 0;
while (i < n)
    invariant 0 <= i;
{
    i := i + 1;
}

// problem can only say what we tell it not what the code does
var i := 0;
while (i < n)
invariant 0 <= i <= n;
{
    i := i + 1;
}

assert i == n; // is true now
```

We can derive a invariant that we want to caluclate by going backwards, we want return == fib(n), should be fib(i) == fib(n) and b == fib(i), we also have a == fib(i - 1), we add if(n == 0) speical case for start

``` dafny
function fib(n: nat): nat
{
    if n == 0 then 0 else
    if n == 1 then 1 else
    fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
    ensures b == fib(n);
{
    if (n == 0) { return 0; }
    var i := 1;
    var a := 0;
    
    b := 1;
    while (i < n)
        invariant 0 < i <= n;
        invariant a == fib(i - 1);
        invariant b == fib(i);
    {
        a, b := b, a + b;
        i := i + 1;
    }
}
```
### Termination
#### Dereases
- Sometiems you need to help dafny to se that the program terminates
- We want to prove that we have a bound and that we are going there
- bound can be dynamic but must converge
``` dafny
while (0 < i)
    invariant 0 <= i;
    decreases i;
{
    i := i - 1;
}

while (i < n)
    invariant 0 <= i <= n;
    decreases n - i;
{
    i := i + 1;
}
```

- Also problem with recursion, cant know if ends
```
function fib(n: nat): nat
    decreases n; // it can guess this but sometimes it needs it
{
    . . .
}
```


### Types

nat: natrual numbers (non-negative)


