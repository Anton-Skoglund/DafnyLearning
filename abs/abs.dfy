// method definition of function 
// f(x) = x'
method Abs ( x : int ) returns ( x': int )
    // post condition is that x' >= 0
    ensures x' >= 0
    // precondtion that is is a valid number
    ensures ( x < 0 && x' == -1* x ) || ( x' == x )

    // calculation
    {
        // set x' to x
        x' := x ;
        // if x' < 0 set x' = -1 * x
        if ( x' < 0 ) { x' := x' * -1; }
    }

    // return atomatic
 