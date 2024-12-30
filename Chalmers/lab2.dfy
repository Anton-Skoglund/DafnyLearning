// class CircularMemory
// This class implements a circular buffer with 2 int typed pointers
class CircularMemory
{
  var cells : array<int>
  var read_position : int
  var write_position : int
  var isFlipped : bool

  constructor Init(cap : int)
    requires cap > 0
    ensures Valid()
  {
    cells := new int[cap];
    read_position, write_position := 0, 0;
    isFlipped := false; 
  }

  // Valid is the class invariant we would like to maintain
  // for any CircularMemory at any moment of its lifetime
  predicate Valid()
    reads this, this.cells
  {

  // Think of some constraints on: 
  // 1. cells.Length? Not <= 0
  // 2. write_position? 0 < WP < size
  // 3. read_position? 0 < RP < size 
  // (WP >= RP || isFlipped) 
    cells.Length > 0 && 
    0 <= write_position < cells.Length && 
    0 <= read_position < cells.Length &&
    ((write_position >= read_position) || (isFlipped && ((write_position <= read_position))))
  }

  // A predicate indicating no more Read available
  predicate isEmpty()
    reads this, this.cells
    requires Valid()
  {
    // read_position >= write_position
    ((forall i :: read_position <= i < cells.Length ==> cells[i] == 0) && 
      (forall i :: 0 <= i < write_position ==> cells[i] == 0)) 
    
    ||
    
    // read_position < write_position
    forall i :: read_position <= i < write_position ==> cells[i] == 0
  }

  //A predicate indicating no more Write should be allowed
  predicate isFull() // forall i :: 0 <= i < cells.Length ==> cells[i] != 0 // :')

    reads this, this.cells
    requires Valid()
  {
     // read_position >= write_position
    ((forall i :: read_position <= i < cells.Length ==> cells[i] != 0) && 
      (forall i :: 0 <= i < write_position ==> cells[i] != 0)) 
    
    ||
    
    // read_position < write_position
    forall i :: read_position <= i < write_position ==> cells[i] != 0
  }

method Read() returns (isSuccess : bool, content : int)
    modifies this, this.cells

    requires Valid()
    requires 0 < read_position < cells.Length
    

    ensures Valid()
    ensures cells.Length == old(cells.Length)

    ensures isSuccess ==> (0 == cells[old(read_position)]  && (read_position == old(read_position) + 1 || read_position == 0) )
    ensures!isSuccess ==> read_position == old(read_position)
  {
    if(isFlipped)
    {
      if(read_position == write_position){
        isFlipped := false; 
        return false, 0;
      }
      
      var read_value: int := cells[read_position];
      cells[read_position] := 0;

      if(read_position == cells.Length - 1){
        read_position := 0;
      }else{
        read_position := read_position + 1;
      }
      return true, read_value;    
    }
    else // not flipped
    {
      if(read_position < write_position){
        var read_value: int := cells[read_position];
        cells[read_position] := 0;
        
        if(read_position == cells.Length - 1){
          read_position := 0;
        }else{
          read_position := read_position + 1;
        }

        return true, read_value;
      }else{
        return false, 0; 
      }
    }
  }

  method Write(input : int) returns (isSuccess : bool)
    modifies this, this.cells
    
    requires Valid()
    
    ensures Valid()
    ensures cells.Length == old(cells.Length)
    // isFlipped == true && write_position == read_position
    ensures !isSuccess ==> write_position == old(write_position) && 
                            old(cells) == cells
    // else 
    ensures  isSuccess ==> (write_position == old(write_position) + 1 || write_position == 0) && 
                            (cells[old(write_position)] == input)
  {
    if(isFlipped)
    {
      if(write_position < read_position){
        cells[write_position] := input;
        write_position := write_position + 1;
        return true;
      }
      return false;
    }
    else // not flipped
    {
      if(write_position == cells.Length - 1){ // When write position is at last available index
        cells[write_position] := input;
        write_position := 0;
        isFlipped := true;
        return true;
        
      }else { // When write position >= read position && wp != cells.Length - 1
        cells[write_position] := input;
        write_position := write_position + 1;
        return true;
      }
    }
  }


  method DoubleCapacity()
    modifies `cells

    requires Valid() 

    requires Valid()
    ensures Valid()
    ensures cells.Length == 2 * old(cells.Length)
    ensures read_position == old(read_position)
    ensures write_position == old(write_position)
    ensures forall j : int :: 0 <= j < old(cells.Length) ==> cells[j] == old(cells[j])
    ensures forall j : int :: old(cells.Length) <= j < cells.Length ==> cells[j] == 0
  {
    var old_length: int := cells.Length;

    var new_array: array<int> := new int[2 * old_length];
    var old_cells: array<int> := new int[old_length];

    var i: int := 0;
    while i < old_length
        invariant 0 <= i <= old_length
        invariant cells.Length == old_length
        invariant new_array.Length == 2 * old_length
        invariant forall j :: 0 <= j < i ==> new_array[j] == cells[j] 
        invariant cells[..] == old(cells)[..]

        decreases old_length - i
    {
        new_array[i] := cells[i];
        old_cells[i] := cells[i];
        assert new_array[i] == cells[i];
        i := i + 1;
        
    }

    assert forall j : int :: 0 <= j < old_length ==> new_array[j] == cells[j]; 


    while i < new_array.Length
        invariant old_length <= i <= new_array.Length
        invariant new_array.Length == 2 * old_length
        invariant cells.Length == old_length
        invariant forall j :: 0 <= j < old_length ==> new_array[j] == cells[j] 
        invariant forall j :: old_length <= j < i ==> new_array[j] == 0 
        invariant cells[..old_length] == old(cells)[..old_length]

        
        decreases new_array.Length - i
    {
        new_array[i] := 0;
        i := i + 1;
    }

    assert forall j : int :: 0 <= j < old_length ==> new_array[j] == cells[j];

    cells := new_array;
    assert cells[..old_length] == old(cells)[..old_length];
  }
}