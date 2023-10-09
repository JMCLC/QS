
module Ex3 {


class Node {

  var data : int 
  var next : Node? 

  ghost var list : seq<int>
  ghost var footprint : set<Node>

  ghost function Valid() : bool 
    reads this, footprint
    decreases footprint
  {
    (this in footprint) &&
    ((next == null) ==> list == [ data ] && footprint == { this }) &&
    ((next != null) ==> 
      (next in footprint) && 
      footprint == next.footprint + { this } && 
      (this !in next.footprint) &&
      list == [ data ] + next.list &&
      next.Valid())
  }

  constructor (val : int) 
    ensures Valid() 
      && next == null && list == [ data ] 
      && footprint == { this } 
      && val == data 
  {
    this.data := val; 
    this.next := null; 
    this.list := [ val ]; 
    this.footprint := { this };
  } 

  method prepend (val : int) returns (r : Node)
    requires Valid()
    ensures r.Valid()
    ensures r.list == [ val ] + this.list
    ensures r.footprint == { r } + this.footprint
    ensures fresh(r) 
  {
    r := new Node(val); 
    r.next := this; 
    r.footprint := { r } + this.footprint; 
    r.list := [ val ] + this.list;  
    return; 
  }

  // Ex1
  method reverse(tail : Node?) returns (r : Node)
    requires Valid()
    requires tail != null ==> tail.Valid() && this.footprint * tail.footprint == {}
    ensures tail == this.next && r.Valid() && Valid()
    ensures tail == null ==> r.list == reverseList(old(this.list))
    ensures tail != null ==> next.Valid() && tail in footprint && r.list == reverseList(old(this.list)) + tail.list
    modifies footprint
    decreases footprint
  {
    var old_next := this.next; 
    this.next := tail; 
    this.footprint := {this};
    this.list := [data];
    if (tail != null) {
      this.footprint := {this} + tail.footprint; 
      this.list := [data] + tail.list;
    }
    if (old_next == null) {
      r := this; 
      return;
    } else {
      r := old_next.reverse(this);
      return; 
    }
  }
}

function reverseList(s: seq<int>): seq<int> {
  if s == [] then []
  else reverseList(s[1..]) + [s[0]]
}

// Ex2
method ExtendList(lst : Node?, v : int) returns (r : Node)
  requires lst != null ==> lst.Valid()
  ensures lst == null ==> r.footprint == {r} && r.list == [v]
  ensures lst != null ==> r.footprint == {r} + old(lst.footprint) && r.list == [v] + old(lst.list) 
  ensures r.Valid()
{
  if (lst != null) {
    r := lst.prepend(v);
  } else {
    r := new Node(v);
  }
}

}