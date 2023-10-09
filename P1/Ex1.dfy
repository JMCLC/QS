datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)

datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)

function serialise<V>(t : Tree<V>) : seq<Code<V>> 
  decreases t 
{
  match t {
    case Leaf(v) => [ CLf(v) ]
    case SingleNode(v, t) => serialise(t) + [ CSNd(v) ]
    case DoubleNode(v, t1, t2) => serialise(t2) + serialise(t1) + [ CDNd(v) ]
  }
}

// Ex 1
function deserialiseAux<V>(cs: seq<Code<V>>, trees: seq<Tree<V>>) : seq<Tree<V>>
  requires |cs| > 0 || |trees| > 0
  ensures |deserialiseAux(cs, trees)| > 0
  decreases cs
{
  if (cs == []) then trees
  else match cs[0] {
    case CLf(v) => deserialiseAux(cs[1..], [Leaf(v)] + trees)
    case CSNd(v) =>
      if |trees| >= 1 then deserialiseAux(cs[1..], [SingleNode(v, trees[0])] + trees[1..])
      else deserialiseAux(cs[1..], [Leaf(v)])
    case CDNd(v) =>
      if |trees| >= 2 then deserialiseAux(cs[1..], [DoubleNode(v, trees[0], trees[1])] + trees[2..])
      else deserialiseAux(cs[1..], [Leaf(v)])
  }
}

function deserialise<V>(cs : seq<Code<V>>): seq<Tree<V>>
  requires |cs| > 0
{
  deserialiseAux(cs, [])
}

// Ex 2
method testSerialise() {
  // Test 1
  var tree1 := SingleNode(2, SingleNode(44, Leaf(3)));
  var treeSerialise1 := serialise(tree1);
  assert treeSerialise1 == [CLf(3), CSNd(44), CSNd(2)];
  // Test 2
  var tree2 := DoubleNode(2, Leaf(44), Leaf(1));
  var treeSerialise2 := serialise(tree2);
  assert treeSerialise2 == [CLf(1), CLf(44), CDNd(2)];
  // Test 3
  var tree3 := DoubleNode(2, Leaf(44), SingleNode(1, Leaf(3)));
  var treeSerialise3 := serialise(tree3);
  assert treeSerialise3 == [CLf(3), CSNd(1), CLf(44), CDNd(2)];
}

// Ex 3
method testDeserialise() {
  // Test 1
  var treeSerialise1 := [CLf(3), CSNd(44), CSNd(2)];
  var tree1 := deserialise(treeSerialise1);
  assert tree1 == [SingleNode(2, SingleNode(44, Leaf(3)))];
  // Test 2
  var treeSerialise2 := [CLf(1), CLf(44), CDNd(2)];
  var tree2 := deserialise(treeSerialise2);
  assert tree2 == [DoubleNode(2, Leaf(44), Leaf(1))];
  // Test 3
  var treeSerialise3 := [CLf(3), CSNd(1), CLf(44), CDNd(2)];
  var tree3 := deserialise(treeSerialise3);
  assert tree3 == [DoubleNode(2, Leaf(44), SingleNode(1, Leaf(3)))];
}

method Main() {
  testDeserialise();
}

// Ex 4
lemma SerialiseLemmaAux<V>(t: Tree<V>, codes: seq<Code<V>>, trees: seq<Tree<V>>)
  ensures deserialiseAux(serialise(t) + codes, trees) == deserialiseAux(codes, [t] + trees)
{
  match t {
    case Leaf(v) =>
      calc {
        deserialiseAux(serialise(t) + codes, trees);
          ==
            deserialiseAux([CLf(v)] + codes, trees);
          ==
            deserialiseAux(codes, [Leaf(v)] + trees);
          ==
            deserialiseAux(codes, [t] + trees);
      }
    case SingleNode(v, t1) =>
      assert serialise(t1) + [CSNd(v)] + codes == serialise(t1) + ([CSNd(v)] + codes);
      calc {
        deserialiseAux(serialise(t) + codes, trees);
          ==
            deserialiseAux(serialise(SingleNode(v, t1)) + codes, trees);
          ==
            deserialiseAux(serialise(t1) + ([CSNd(v)] + codes), trees);
          == {SerialiseLemmaAux(t1, [CSNd(v)] + codes, trees);}
            deserialiseAux([CSNd(v)] + codes, [t1] + trees);
          ==
            deserialiseAux(codes, [SingleNode(v, t1)] + trees);
          ==
            deserialiseAux(codes, [t] + trees);
      }
    case DoubleNode(v, t1, t2) =>
      assert serialise(t2) + serialise(t1) + [CDNd(v)] + codes == serialise(t2) + (serialise(t1) + [CDNd(v)] + codes);
      assert serialise(t1) + [CDNd(v)] + codes == serialise(t1) + ([CDNd(v)] + codes);
      assert [t1] + ([t2] + trees) == [t1, t2] + trees;
      calc {
        deserialiseAux(serialise(t) + codes, trees);
          ==
            deserialiseAux(serialise(t2) + (serialise(t1) + [CDNd(v)] + codes), trees);
          == {SerialiseLemmaAux(t2, serialise(t1) + [CDNd(v)] + codes, trees);}
            deserialiseAux(serialise(t1) + ([CDNd(v)] + codes), [t2] + trees);
          == {SerialiseLemmaAux(t1, ([CDNd(v)] + codes), [t2] + trees);}
            deserialiseAux([CDNd(v)] + codes, [t1] + ([t2] + trees));
          ==
            deserialiseAux([CDNd(v)] + codes, [t1, t2] + trees);
          == 
            deserialiseAux(codes, [DoubleNode(v, t1, t2)] + trees);
          ==
            deserialiseAux(codes, [t] + trees);
      }
  }
}

lemma SerialiseLemma<V>(t : Tree<V>)
  ensures deserialise(serialise(t)) == [t] 
{
  assert serialise(t) + [] == serialise(t);
  calc {
    deserialise(serialise(t));
      ==
        deserialiseAux(serialise(t) + [], []);
      == {SerialiseLemmaAux(t, [], []);}
        deserialiseAux([], [t] + []);
      ==
        deserialiseAux([], [t]);
      ==
        [t];
  }
}