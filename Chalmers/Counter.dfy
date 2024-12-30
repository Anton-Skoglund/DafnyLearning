class Counter {

  var value : int
  
  constructor init() 
  ensures value == 0
  {
    value := 0 ;
  }
  
  method getValue() returns (x:int)
    ensures x == this.value
  {
    x := value ;
  }
  
  method inc()
    modifies this
    ensures value == old(value) + 1
  {
    
    value := value + 1;
  }
  
  method dec()
    modifies this
    ensures value == old(value) - 1

  { 
    value := value - 1 ;
  }
  
   
  method Main ()
  {
   var count := new Counter.init() ;
   count.inc();
   count.inc();
   count.dec();
   count.inc();

   var aux : int := count.getValue();
   assert (aux == 2) ;
  }
}