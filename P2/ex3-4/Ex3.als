sig HeadNode {
    var frst: lone Node,
    var lst: lone Node
}

sig Node {
    var nnext: lone Node,
    var nprev: lone Node
}

// C1: The First node of a linked list can not have a previous node
fact C1 {
    always no HeadNode.frst.nprev
}

// C2: The Last node of a linked list can not have a next node
fact C2 {
    always no HeadNode.lst.nnext
}

// C3: A Node must always have a previous node if it is not the first one in a linked list
fact C3 {
    always all n: Node | (n !in HeadNode.frst && n in HeadNode.frst.*nnext) implies some n.nprev
}

// C4: A Node must always have a next node if it is not the last one in a linked list
fact C4 {
    always all n: Node | (n !in HeadNode.lst && n in HeadNode.lst.*nprev) implies some n.nnext
}

// C5: The last node of a linked list must be reachable from the first node
fact C5 {
    always all l: HeadNode | l.lst in l.frst.*nnext
}

// C6: The current node has to be the previous node of the one it is connected to
fact C6 {
    always nnext = ~nprev
}

// C7: A Node can only belong to a single linked list
fact C7 {
    always all n: Node | #(n.(~frst + ~lst)) <= 1 
}

// C8: A Node can not be reachable from the next node
fact C8 {
    always all n: Node | n !in n.^nnext
}

// C9: A Node can not be reachable from the previous node
fact C9 {
    always all n: Node | n !in n.^nprev
}

// C10: If a Node is free it can not be connected to another node
fact C10 {
    always all n: Node | n !in HeadNode.frst.*nnext implies n.nnext = none && n.nprev = none 
}

pred insertFirst[n: Node, hn: HeadNode] {
    hn.frst' = n
    hn.frst.nprev' = n
    n.nnext' = hn.frst
    no (n.nprev')
}

pred insertSingleton[n: Node, hn: HeadNode] {
    hn.frst' = n
    hn.lst' = n
    no (n.nprev')
    no (n.nnext')
}

pred insert[n: Node, hn: HeadNode] {
    // Pre-conditions:
    // - The node can not belong to any linked list and must be free
    no (n.nnext)
    no (n.nprev)
    all hn1: HeadNode | n !in hn1.(frst + lst)

    // Post-conditions:
    // - If there is no node in the linked list it gets added as the frst and lst value of it
    hn.frst = none implies insertSingleton[n, hn]
    // - Else if there is already any Node it gets added as the frst and the previous frst Node gets edited to have the new one before it
    hn.frst != none implies insertFirst[n, hn]

    // Frame-conditions:
    // - All the linked lists different from the one received stay the same
    all hn1: HeadNode | hn1 != hn implies hn1.frst' = hn1.frst && hn1.lst' = hn1.lst
    // - All the nodes that are not the received one or the frst of the linked list (the frst could be none) stay the same
    all n1: Node | (n1 != n && n1 != hn.frst) implies n1.nnext' = n1.nnext && n1.nprev' = n1.nprev
}

pred removeFirst[n: Node, hn: HeadNode] {
    no (n.nprev')
    no (n.nnext')
    no (n.nnext.nprev')
    hn.frst' = n.nnext
}

pred removeSingleton[n: Node, hn: HeadNode] {
    no (hn.frst')
    no (hn.lst')
    no (n.nnext')
    no (n.nprev')
}

pred remove[n: Node, hn: HeadNode] {
    // Pre-conditions:
    // - The node must belong to the linked list received
    n in hn.frst

    // Post-conditions:
    // - If the last value of the list is the one received the linked list should be emptied
    n = hn.lst implies removeSingleton[n, hn]
    // - Else the Node received is removed and the one that was next to it gets put as the first one in the list
    n != hn.lst implies removeFirst[n, hn]

    // Frame-conditions:
    // - All the linked lists different from the one received stay the same
    all hn1: HeadNode | hn1 != hn implies hn1.frst' = hn1.frst && hn1.lst' = hn1.lst
    // - All the nodes that are not the received one or the next one (it could be none) stay the same
    all n1: Node | (n1 != n && n1 != n.nnext) implies n1.nnext' = n1.nnext && n1.nprev' = n1.nprev
}

// EX 3.2
run {} 
for exactly 2 HeadNode, exactly 5 Node

// EX 3.4:
// - Insert Trace
run insert for 2 HeadNode, 3 Node

// - Remove Trace
run remove for 2 HeadNode, 3 Node