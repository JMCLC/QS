include "Ex3.dfy"


module Ex4 {


import Ex3=Ex3

class Queue {

  var lst1 : Ex3.Node?
  var lst2 : Ex3.Node?

  ghost var list1: multiset<int>
  ghost var list2: multiset<int>

  ghost var footprint1: set<Ex3.Node>
  ghost var footprint2: set<Ex3.Node>

  // Ex1
  ghost function Valid() : bool
    reads 
      this,
      lst1, 
      lst2, 
      if lst1 == null then {} else lst1.footprint,
      if lst2 == null then {} else lst2.footprint
  {
    (lst1 != null ==>
      this.footprint1 == lst1.footprint &&
      lst1.Valid() &&
      list1 == multiset(lst1.list)
    ) &&
    (lst1 == null ==>
      this.footprint1 == {} &&
      list1 == multiset{}
    ) &&
    (lst2 != null ==>
      this.footprint2 == lst2.footprint &&
      lst2.Valid() &&
      list2 == multiset(lst2.list)
    ) &&
    (lst2 == null ==>
      this.footprint2 == {} &&
      list2 == multiset{}
    )
  }

  // Ex2 
  constructor () 
  {
    this.lst1 := null; 
    this.lst2 := null;  
    this.footprint1 := {};
    this.footprint2 := {};
    this.list1 := multiset{};
    this.list2 := multiset{};
  } 

  // Ex3.1
  method push(val : int)
    requires Valid()
    ensures Valid()
    modifies this, this.footprint1
  {
    lst1 := Ex3.ExtendList(lst1, val);
    this.list1 := multiset(lst1.list);
    this.footprint1 := lst1.footprint;
  }

  // Ex3.2
  method pop() returns (r : int)
    requires Valid() && (lst2 == null ==> lst1 != null)
    ensures old(lst2) != null ==>
      old(lst1) == lst1 &&
      (old(lst2.next) == null ==> 
        footprint2 == {} &&
        lst2 == null
      ) &&
      (old(lst2.next) != null ==>
        footprint2 == old(lst2.next.footprint)
      )
    ensures old(lst2) == null ==>
      old(lst1).Valid() &&
      (old(lst1.next) == null ==>
        footprint2 == {}
      )
    ensures old(lst2) == null ==> lst1 == null
    ensures old(lst2) != null ==> r == old(lst2.data)
    ensures Valid()
    modifies this, this.footprint2, this.footprint1
  {
    if (lst2 == null) {
      lst2 := lst1.reverse(null); 
      lst1 := null;
      footprint1 := {};
      footprint2 := lst2.footprint;
      list1 := multiset{};
      list2 := multiset(lst2.list);
    }

    r := lst2.data;
    footprint2 := footprint2 - {lst2};
    list2 := list2 - multiset([lst2.data]);
    lst2 := lst2.next;
  }
}

}