
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
    requires tail != null ==> tail.Valid() ==> this !in footprint
    requires next != null ==> next.Valid() ==> this !in footprint
    ensures this.next == tail
    // ensures tail != null ==> tail.footprint != old(tail.footprint)
    ensures tail != null ==> list == [data] + tail.list && footprint == {this} + tail.footprint
    // ensures tail != null ==> r.list == [data] + tail.list
    // ensures tail != null ==> r.footprint == {this} + tail.footprint
    ensures old(next) != null ==> old(next).footprint == {old(next)} + this.footprint
    ensures old(next) != null ==> old(next).list == [old(next).data] + this.list
    ensures tail == null ==> list == [data]
    ensures tail == null ==> footprint == {this}
    ensures old(next) == null ==> r == this
    ensures Valid()
    ensures r.Valid()
    modifies footprint
    decreases footprint
  {
    var old_next := this.next; 
    this.next := tail; 
    this.footprint := {this};
    this.list := [data];
    if (tail != null) {
      this.footprint := tail.footprint + {this} ; 
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

  // function reverseList(tail: Node?, cur: Node): seq<int>
  //   requires tail.Valid()
  // {
  //   if tail == null then [cur.data]
  //   else [cur.data] + tail.list
  // }

  // function reverseFootprint(tail: Node, cur: Node): set<Node>
  // {
  //   if tail == null then {cur}
  //   else {cur} + tail.footprint
  // }


  // method reverse(tail : Node?) returns (r : Node)
  //   requires Valid()
  //   ensures fresh(footprint)
  //   ensures tail == null ==> this.footprint == {this} && this.list == [data]
  //   ensures tail != null ==> this.footprint == tail.footprint + {this} && this.list == tail.list + [data]
  //   ensures old(next) != null ==> old(next).list == list + [old(next.data)]
  //   ensures old(next) != null ==> old(next).footprint == footprint + {old(next)}
  //   ensures Valid()
  //   ensures r.Valid()
  //   modifies footprint
  //   decreases footprint
  // {
  //   var old_next := this.next;
  //   this.next := tail;
  //   this.footprint := {this};
  //   this.list := [data];
  //   if (tail != null) {
  //     this.footprint := tail.footprint + {this} ; 
  //     this.list := [data] + tail.list; 
  //   }
  //   if (old_next == null) {
  //     r := this;
  //     return; 
  //   } else {
  //     r := old_next.reverse(this);
  //     return;  
  //   }
  // }
}

// Ex2

method ExtendList(lst : Node?, v : int) returns (r : Node)
  requires lst != null ==> lst.Valid()
  ensures lst == null ==> r.footprint == {r}
  ensures lst != null ==> r.footprint == {r} + lst.footprint
  ensures lst == null ==> r.list == [r.data]
  ensures lst != null ==> r.list == [r.data] + lst.list
  ensures r.Valid()
{
  if (lst != null) {
    r := lst.prepend(v);
  } else {
    r := new Node(v);
  }
}

}