sig Node {
    var nprev: lone Node,
    var nnext: lone Node
}

// Define the HNode signature
sig HNode {
    var first: one Node,  // First node in the list
    var last: one Node    // Last node in the list
}

// The first node does not have a previous node, and the last node does not have a next node
fact FirstLastNodes {
    always all l: HNode | no l.first.nprev && no l.last.nnext
}

fact SingleDLLorFree {
   always all n: Node | 
        lone l: HNode | 
            n in (l.first + l.first.*nnext + l.last + l.last.*nprev)
}

// No node is its own next or previous node
fact NoSelfPointing {
   always  no n: Node | n = n.nnext or n = n.nprev
}

// Consistency of Connections
fact ConsistencyOfConnections {
   always all n1, n2 : Node | (n1 in n2.^nnext implies n2 in n1.^nprev) and (n1 in n2.^nprev implies n2 in n1.^nnext)
}

// Free nodes should not be connected to any other node
fact FreeNodesAreLone {
    always all n: Node | (no l: HNode | n = l.first or n in l.first.^nnext or n = l.last or n in l.last.^nprev) implies (no n.nnext and no n.nprev)
}

// Nodes inside of a list are connected to each other
fact NodesAreConnected {
   always all l: HNode | l.last in l.first.*nnext and l.first in l.last.*nprev
}


// C1: The First node of a linked list can not have a previous node
// fact C1 {
//     always no HNode.first.nprev
// }

// C2: The Last node of a linked list can not have a next node
// fact C2 {
//     always no HNode.last.nnext
// }

// C3: A Node must always have a previous node if it is not the first one in a linked list
// fact C3 {
//     always all n: Node | (n !in HNode.first && n in HNode.first.*nnext) implies some n.nprev
// }

// C4: A Node must always have a next node if it is not the last one in a linked list
// fact C4 {
//     always all n: Node | (n !in HNode.last && n in HNode.last.*nprev) implies some n.nnext
// }

// C5: The last node of a linked list must be reachable from the first node
// fact C5 {
//     always all l: HNode | l.last in l.first.*nnext
// }

// C6: The current node has to be the previous node of the one it is connected to
// fact C6 {
//     always nnext = ~nprev
// }

// C7: A Node can only belong to a single linked list
// fact C7 {
//     always all n: Node | #(n.(~first + ~last)) <= 1 
// }

// C8: A Node can not be reachable from the next node
// fact C8 {
//     always all n: Node | n !in n.^nnext
// }

// C9: A Node can not be reachable from the previous node
// fact C9 {
//     always all n: Node | n !in n.^nprev
// }

// C10: If a Node is free it can not be connected to another node
// fact C10 {
//     always all n: Node | n !in HNode.first.*nnext implies n.nnext = none && n.nprev = none 
// }

pred insertFirst[n: Node, hn: HNode] {
    hn.first' = n
    hn.first.nprev' = n
    n.nnext' = hn.first
    no (n.nprev')
}

pred insertSingleton[n: Node, hn: HNode] {
    hn.first' = n
    hn.last' = n
    no (n.nprev')
    no (n.nnext')
}

pred insert[n: Node, hn: HNode] {
    // Pre-conditions:
    // - The node can not belong to any linked list and must be free
    no (n.nnext)
    no (n.nprev)
    all hn1: HNode | n !in hn1.(first + last)

    // Post-conditions:
    // - If there is no node in the linked list it gets added as the first and last value of it
    hn.first = none implies insertSingleton[n, hn]
    // - Else if there is already any Node it gets added as the first and the previous first Node gets edited to have the new one before it
    hn.first != none implies insertFirst[n, hn]

    // Frame-conditions:
    // - All the linked lists different from the one received stay the same
    all hn1: HNode | hn1 != hn implies hn1.first' = hn1.first && hn1.last' = hn1.last
    // - All the nodes that are not the received one or the first of the linked list (the first could be none) stay the same
    all n1: Node | (n1 != n && n1 != hn.first) implies n1.nnext' = n1.nnext && n1.nprev' = n1.nprev
}

// pred insertSingle[n: Node, hn: HNode] {
//     hn.first' = n
//     hn.last' = n
//     n.nnext' = none
//     n.nprev' = none 
// }

// // Inserting a node into a list with nodes
// pred insertNormal[n: Node, hn: HNode] {
//     n.nprev' = hn.last
//     hn.last.nnext' = n
//     hn.last' = n
//     n.nnext' = none
// }

// pred insert[n: Node, hn: HNode] {
//     // Pre-conditions
//     no (n.nprev)
//     no (n.nnext)
//     all hn_new : HNode | n !in hn_new.(first + last)
    
//     // Post-conditions
//     (no (hn.first) implies insertSingle[n,hn]) or (some hn.first implies insertNormal[n, hn])
    

//     // Frame conditions ( relations that are not modified by the operation )
//     all n1: Node | (n1 != n && n1 != hn.last) implies n1.nnext' = n1.nnext && n1.nprev' = n1.nprev
//     all hn1: HNode | (hn1 != hn) implies hn1.first' = hn1.first && hn1.last' = hn1.last
    
        
    
// }

// run {some nnext && some nprev} for exactly 2 HNode, exactly 6 Node

run insert for 2 HNode , 3 Node