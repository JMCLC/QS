sig HeadNode {
    var frst: one Node,
    var lst: one Node
}

sig Node {
    var nnext: lone Node,
    var nprev: lone Node
}

// C1: The First node of a linked list can not have a previous node
fact C1 {
    no HeadNode.frst.nprev
}

// C2: The Last node of a linked list can not have a next node
fact C2 {
    no HeadNode.lst.nnext
}

// C3: A Node must always have a previous node if it is not the first one in a linked list
fact C3 {
    all n: Node | (n !in HeadNode.frst) implies some n.nprev
}

// C4: A Node must always have a next node if it is not the last one in a linked list
fact C4 {
    all n: Node | (n !in HeadNode.lst) implies some n.nnext
}

// C5: The last node of a linked list must be reachable from the first node
fact C5 {
    all l: HeadNode | l.lst in l.frst.*nnext
}

// C6: The current node has to be the previous node of the one it is connected to
fact C6 {
    nnext = ~nprev
}

// C7: A Node can only belong to a single linked list
fact C7 {
    all n: Node | #(n.(~frst + ~lst)) <= 1
}

// C8: A Node can not be reachable from the next node
fact C8 {
    all n: Node | n !in n.^nnext
}

// C9: A Node can not be reachable from the previous node
fact C9 {
    all n: Node | n !in n.^nprev
}

pred insert[n: Node, hn: HeadNode] {
    // Pre-conditions:
    // - The node can not belong to any linked list
    all hn1: HeadNode | n !in hn1.frst.*nnext

    // Post-conditions:
    // - If there is no first value then node will be the first and last node
    hn.frst = none implies (hn.frst' = n && hn.lst' = n);
    // - Else it is appended to the list as the last one
    hn.frst != none implies (hn.lst' = n && n.nprev' = hn.lst && hn.lst.nnext' = n)

    // Frame-conditions:
    // - All head nodes that are not the received maintain the same frst and lst value
    all hn1: HeadNode | hn1 != hn implies (hn1.frst' = hn1.frst && hn1.lst' = hn1.lst)
    // - All nodes that are not the received or the last one of the list are not changed
    all n1: Node | (n1 != n && hn.lst != n1) implies (n1.nprev' = n1.nprev && n1.nnext' = n1.nnext)
}

pred remove[n: Node, hn: HeadNode] {
    // Pre-conditions:
    // - The node cant not belong to any linked list that is not the received
    all hn1: HeadNode | hn1 != hn implies no (hn1.frst.*nnext & n)
    // - The node must belong to the linked list received
    one (hn.frst.*nnext & n)

    // Post-conditions:
    // - If the node is the first value of the list than it gets passed to the next
    hn.frst = n implies (hn.frst' = n.nnext && n.nnext.nprev' = none)
    // - Else if the node is the last value then it gets passed to the previous
    hn.lst = n implies (hn.lst' = n.nprev && n.nprev.nnext' = none)
    // - Else it is a node in the rest of the linked list
    (hn.frst != n && hn.lst != n) implies (n.nprev.nnext' = n.nnext && n.nnext.nprev' = n.nprev)

    // Frame-conditions:
    // - All head nodes that are not the received maintain the same frst and lst value
    all hn1: HeadNode | hn1 != hn implies (hn1.frst' = hn1.frst && hn1.lst' = hn1.lst)
    // - All nodes that are not the received or the last one of the list are not changed
    all n1: Node | (n1 != n && n1 != n.nnext && n1 != n.nprev) implies (n1.nprev' = n1.nprev && n1.nnext' = n1.nnext)
}

// EX 3.2
// run {} 
// for exactly 2 HeadNode, exactly 5 Node

pred TestInsert {
    ((some frst) and (some lst) and (some nnext) and (some nprev))
    and
    (eventually once (some n: Node, hn: HeadNode | insert[n, hn]))   
}

run TestInsert for 5 but 10 steps

// LEGACY CODE
// pred Init[] {
//     no frst
//     no lst
//     no nnext
//     no nprev
// }

// pred Stutter[] {
//     frst' = frst
//     lst' = lst
//     nnext' = nnext
//     nprev' = nprev
// }

// pred Trans[] {
//     some n: Node, hn: HeadNode | insert[n, hn]
//     or
//     some n: Node, hn: HeadNode | remove[n, hn]
//     or
//     Stutter[]
// }

// pred System[] {
//     Init[]
//     and
//     always Trans[]
// }

// fact SystemFact {
//     System[]
// }