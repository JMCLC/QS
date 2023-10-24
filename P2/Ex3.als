sig List {
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
//     List.lst.nnext = none
// }

// fact noPrevOnLast {
//     List.frst.nprev = none
// }

fact ifNextThenInPrev {
    all n1, n2: Node | n2 in n1.nnext implies n1 in n2.nprev
} 

run {}

for exactly 1 List, exactly 5 Node