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
// function deserialise<V>(cs : seq<Code<V>>) : Tree<V> -- Old versioj
// {
//   // ToDo
// }
function deserialise<V>(cs : seq<Code<V>>) : seq<Tree<V>>
// {
//   // ToDo
// }

// Ex 2


// Ex 3 

// Ex 4 

lemma SerialiseLemma<V>(t : Tree<V>)
  ensures deserialise(serialise(t)) == [t] 
{
  // ToDo
}





