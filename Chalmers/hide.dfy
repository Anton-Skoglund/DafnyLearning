method M(x : int, y : int) returns (a : int, b : int) 
  ensures a > b
{
  if (x > y)
   {a:= x;
    b := y;}
  else
   {a := y; 
    b := x;}
}

// You cant prove a post condition if a == b then it will be true


/*
    a > b
    IF: x > y OR Else: x >= y // break it 
    
*/

method M1(x : int, y : int) returns (a : int, b : int) 
  ensures a >= b
{
  if (x > y)
   {a:= x;
    b := y;}
  else
   {a := y; 
    b := x;}
}

method M2(x : int, y : int) returns (a : int, b : int) 
  requires x > y
  ensures a > b
{
  if (x > y)
   {a:= x;
    b := y;}
  else
   {a := y; 
    b := x;}
}

method M3(x : int, y : int) returns (a : int, b : int) 
  ensures a > b || (a == -1 && b == -1)
{
  if (x > y)
   {a:= x;
    b := y;}
  else if(x < y)
   {a := y; 
    b := x;}
    else{
        a := -1;
        b := -1;
    }
}


function fact(n: nat): nat
    requires n >= 1
    decreases n
{
    if n == 1 then 1
    else fact(n-1) * n
}


method ComputeFact(n : nat) returns (res : nat)
  requires n > 0
  ensures res == fact(n)
 {
  res := 1;
  var i := 2;
  while (i <= n)
    invariant i > 0 && res == fact(i - 1) && 1 <= i <= n + 1
    decreases (n - 1)
  {
    res := res * i;
    i := i + 1;
  }
 }