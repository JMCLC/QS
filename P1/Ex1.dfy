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
      if |trees| >= 2 then deserialiseAux(cs[1..], [SingleNode(v, trees[1])] + trees[2..])
      else deserialiseAux(cs[1..], [Leaf(v)])
    case CDNd(v) =>
      if |trees| >= 3 then deserialiseAux(cs[1..], [DoubleNode(v, trees[2], trees[1])] + trees[3..])
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
  // ToDo
}





