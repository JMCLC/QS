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
    reads this, lst1, lst2, if lst1 == null then {} else lst1.footprint, if lst2 == null then {} else lst2.footprint
  {
    (lst1 != null ==> this.footprint1 == lst1.footprint && lst1.Valid() && list1 == multiset(lst1.list))
    &&
    (lst1 == null ==> this.footprint1 == {} && list1 == multiset{})
    &&
    (lst2 != null ==> this.footprint2 == lst2.footprint && lst2.Valid() && list2 == multiset(lst2.list))
    &&
    (lst2 == null ==> this.footprint2 == {} && list2 == multiset{})
  }

  // Ex2 
  constructor ()
    ensures Valid() && lst1 == null && lst2 == null && footprint1 == {} && footprint2 == {} && list1 == multiset{} && list2 == multiset{}
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
    ensures old(lst1) == null ==> list1 == multiset{val}
    ensures old(lst1) != null ==> list1 == multiset{val} + multiset(old(lst1.list))
    ensures Valid()
    modifies this
  {
    this.list1 := multiset([val]);
    if (lst1 != null) {
      list1 := list1 + multiset(lst1.list);
      footprint1 := lst1.footprint;
    }
    lst1 := Ex3.ExtendList(lst1, val);
    footprint1 := footprint1 + {lst1};
  }

  // Ex3.2
  method pop() returns (r : int)
    requires Valid() && (lst2 == null ==> lst1 != null)
    // ensures old(lst2) == null ==> r == Ex3.reverseList(old(lst1.list))[0] && list2 == multiset(old(lst1.list)) - multiset([r])
    ensures old(lst2) != null ==> r == old(lst2.data) && list2 == multiset(old(lst2.list)) - multiset([r]) &&(if old(lst2.next) == null then lst2 == null else lst2 == old(lst2.next))
    ensures Valid()
    modifies this, if lst2 == null then lst1.footprint else {}
  {
    if (lst2 == null) {
      lst2 := lst1.reverse(null); 
      lst1 := null;
      footprint1 := {};
      list1 := multiset{};
    }

    r := lst2.data;
    footprint2 := lst2.footprint - {lst2};
    list2 := multiset(lst2.list) - multiset([r]);
    lst2 := lst2.next;
  }
}

}