function deserialise<T>(codes: seq<Code<T>>): seq<Tree<T>>
    requires |codes| > 0
{
    deserialiseAux(codes, [])
}

function deserialiseAux<T>(codes: seq<Code<T>>, trees: seq<Tree<T>>): seq<Tree<T>>
    requires |codes| > 0 || |trees| > 0
    ensures |deserialiseAux(codes, trees)| > 0
{

}