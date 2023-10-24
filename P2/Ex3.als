sig HeadNode {
    frst: lone Node,
    lst: lone Node
}

sig Node {
    nnext: lone Node,
    nprev: lone Node
}

fact noLoop {
    all n: Node | n !in n.^(nnext + nprev)
}

// fact noNextOnLast {
//     HeadNode.lst.nnext = none
// }

// fact noPrevOnLast {
//     HeadNode.frst.nprev = none
// }

fact ifNextThenInPrev {
    all n1, n2: Node | n2 in n1.nnext implies n1 in n2.nprev
    all n1, n2: Node | n1 in n2.nprev implies n2 in n1.nnext
}

fact lstReachableFromFrst {
    all l: HeadNode | l.lst in l.frst.^nnext
}

run {}

// for exactly 1 HeadNode, exactly 5 Node