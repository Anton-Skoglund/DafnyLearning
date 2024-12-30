
method Q1(){
     var a := new int[6];
     a[0],a[1],a[2],a[3],a[4],a[5] := 1,0,0,0,1,1;
     var b := new int[3];
     b[0],b[1],b[2] := 1,0,1; 
     
     var j,k := 1,3;
     var p,r := 4,5;

     // a) All elements in the range a[j..k] are 0.
     assert(forall i :: j <= i <= k && a[i] == 0);

     // b) All zeros in a occur in the interval a[j..k].                                     
     assert(forall i :: 0 <= i < a.Length && (a[i] == 0 ==> j <= i <= k));

     // c) It is *not* the case that all ones of a occur in the interval in a[p..r]                             
     assert(forall i :: 0 <= i < a.Length && a[i] == 1 ==> p <= i <= r);


     //d) a[0..n-1] contains at least two zeros.
    assert(forall i, j :: 0 <= i, j < a.Length - 1 && a[i] == 0 && a[j] == 0 ==> p <= i <= r);


     //e) b[0..n-1] contains at most two zeros (Note: *not* true about array a). 
     
}   