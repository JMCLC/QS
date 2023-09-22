include "Ex3.dfy"


module Ex4 {


import Ex3=Ex3

class Queue {

  var lst1 : Ex3.Node?
  var lst2 : Ex3.Node? 

  // Ex1
  ghost function Valid() : bool 
  {
    // ToDo  
  }

  // Ex2 
  constructor () 
  {
    this.lst1 := null; 
    this.lst2 := null;  
    // ToDo
  } 

  // Ex3.1
  method push(val : int) 
  {
    lst1 := Ex3.ExtendList(lst1, val);     
  }

  // Ex3.2
  method pop() returns (r : int)
  {

    if (lst2 == null) {
      lst2 := lst1.reverse(null); 
      lst1 := null;
    }

    r := lst2.data; 
    lst2 := lst2.next; 
  }
  
}

}