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


// Ex 3 

// Ex 4 

lemma SerialiseLemma<V>(t : Tree<V>)
  ensures deserialise(serialise(t)) == [t] 
{
  match t {
    case Leaf(v) =>
      calc {
        deserialise(serialise(t));
          ==
            deserialise(serialise(Leaf(v)));
          ==
            deserialise([CLf(v)]);
          ==
            deserialiseAux([CLf(v)], []);
          ==
            deserialiseAux([], [Leaf(v)]);
          ==
            [Leaf(v)];
          ==
            [t];
      }
    case SingleNode(v, t1) =>
      calc {
        deserialise(serialise(t));
          ==
            deserialise(serialise(SingleNode(v, t1)));
          ==
            deserialise(serialise(t1) + [CSNd(v)]);
          ==
            deserialiseAux(serialise(t1) + [CSNd(v)], []);
          ==
            deserialiseAux([CSNd(v)], [t1]);
          ==
            deserialiseAux([], [SingleNode(v, t1)]);
          ==
            [SingleNode(v, t1)];
          ==
            [t];
      }
    case DoubleNode(v, t1, t2) =>
      calc {
        deserialise(serialise(t));
          ==
            deserialise(serialise(DoubleNode(v, t1, t2)));
          ==
            deserialise(serialise(t2) + serialise(t1) + [CDNd(v)]);
          ==
            deserialiseAux(serialise(t2) + serialise(t1) + [CDNd(v)], []);
          ==
            deserialiseAux(serialise(t1) + [CDNd(v)], [t2]);
          ==
            deserialiseAux([CDNd(v)], [t1] + [t2]);
          ==
            deserialiseAux([CDNd(v)], [t1, t2]);
          ==
            deserialiseAux([], [DoubleNode(v, t1, t2)]);
          ==
            [DoubleNode(v, t1, t2)];
          ==
            [t];
      }
  }
}

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
      calc {
        deserialiseAux(serialise(t) + codes, trees);
          ==
            deserialiseAux(serialise(t1) + [CSNd(v)] + codes, trees);
          ==
            deserialiseAux([CSNd(v)] + codes, [t1] + trees);
          ==
            deserialiseAux(codes, [SingleNode(v, t1)] + trees);
          ==
            deserialiseAux(codes, [t] + trees);
      }
    case DoubleNode(v, t1, t2) =>
      calc {
        deserialiseAux(serialise(t) + codes, trees);
          ==
            deserialiseAux(serialise(t2) + serialise(t1) + [CDNd(v)] + codes, trees);
          ==
            deserialiseAux(serialise(t1) + [CDNd(v)] + codes, [t2] + trees);
          ==
            deserialiseAux([CDNd(v)] + codes, [t1] + [t2] + trees);
          ==
            deserialiseAux([CDNd(v)] + codes, [t1, t2] + trees);
          ==
            deserialiseAux(codes, [DoubleNode(v, t1, t2)] + trees);
          ==
            deserialiseAux(codes, [t] + trees);
      }
  }
}