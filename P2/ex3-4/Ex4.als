open Ex3
open util/ordering[Id]

sig OrderedHeadNode extends HeadNode {
}

sig OrderedNode extends Node {
    id: one Id
}

sig Id {}

// C11: An Id must always have a different Ordered Node
fact C11 {
    always all id1: Id | #(id1.~id) = 1 
}

// C12: For all Ordered Nodes that belong to the same Linked List the previous one as an Id smaller than the next one
fact C12 {
    always all on1, on2: OrderedNode | on2 in on1.^nnext implies on1.id.lt[on2.id]
}

fun FirstGreaterId[on: OrderedNode, ohn: OrderedHeadNode]: Id {
    (on.id.nexts[] & ohn.frst.^nnext.id).min[]
}

pred orderedInsertRest[on: OrderedNode, ohn: OrderedHeadNode] {
    on.id.gt[ohn.frst.id] implies all n1: OrderedNode | (n1 in ohn.frst.*nnext && on.id.gt[n1.id] && (on.id.lt[n1.nnext.id] || no (n1.nnext))) implies on.nprev' = n1 && n1.nnext' = on && on.nnext' = n1.nnext && n1.nnext.nprev' = on
    on.id.lt[ohn.frst.id] implies no (on.nprev') && on.nnext' = ohn.frst && ohn.frst' = on && ohn.frst.nprev' = on
    // on.id.lt[ohn.frst.id] implies ohn.frst' = on && ohn.frst.nprev' = on && on.nnext' = ohn.frst && no (on.nprev')
    // on.id.gt[ohn.lst.id] implies ohn.lst' = on && ohn.lst.nnext' = on && on.nprev' = ohn.lst && no (on.nnext')
    // on.id.gt[ohn.frst.id] && on.id.lt[ohn.lst.id] implies 
    // all n1: OrderedNode | n1 in ohn.frst.^nnext && n1.id.lt[on.id] && n1.nnext.id.gt[on.id] implies
    // on.nprev' = n1 && on.nnext' = n1.nnext && n1.nnext' = on && n1.nnext.nprev' = on
    // all on1: OrderedNode | (on1 in ohn.frst.*nnext && on1.id = FirstGreaterId[on, ohn]) implies
    // on1.nprev' = on && on.nnext' = on1 && on.nprev' = on1.nprev && on1.nprev.nnext' = on1
}

pred orderedInsertSingleton[on: OrderedNode, ohn: OrderedHeadNode] {
    ohn.frst' = on
    ohn.lst' = on
    no (on.nprev')
    no (on.nnext')
}

pred orderedInsert[on: OrderedNode, ohn: OrderedHeadNode] {
    // Pre-conditions:
    // - The node can not belong to any linked list and must be free
    no (on.nnext)
    no (on.nprev)
    all ohn1: OrderedHeadNode | on !in ohn1.(frst + lst)

    // Post-conditions:
    // - If there is no node in the linked list it gets added as the frst and lst value of it
    no (ohn.frst) implies orderedInsertSingleton[on, ohn]
    // - Else if there is already any Node it gets added as the frst and the previous frst Node gets edited to have the new one before it
    ohn.frst != none implies orderedInsertRest[on, ohn]

    // Frame-conditions:
    // - All the linked lists different from the one received stay the same
    all ohn1: HeadNode | ohn1 != ohn implies ohn1.frst' = ohn1.frst && ohn1.lst' = ohn1.lst
    // - All the nodes that are not the received one or the frst of the linked list (the frst could be none) stay the same
    all on1: Node | (on1 != on && on1 != ohn.frst) implies on1.nnext' = on1.nnext && on1.nprev' = on1.nprev
}

pred orderedRemoveRest[on: OrderedNode, ohn: OrderedHeadNode] {
    no (on.nprev')
    no (on.nnext')
    on = ohn.frst implies no (on.nnext.nprev') && ohn.frst' = on.nnext
    on = ohn.lst implies no (on.nprev.nnext') && ohn.lst' = on.nprev
    (on != ohn.lst && on != ohn.frst) implies on.nnext.nprev' = on.nprev && on.nprev.nnext' = on.nnext
}

pred orderedRemoveSingleton[on: OrderedNode, ohn: OrderedHeadNode] {
    no (ohn.frst')
    no (ohn.lst')
    no (on.nnext')
    no (on.nprev')
}

pred orderedRemove[on: OrderedNode, ohn: OrderedHeadNode] {
    // Pre-conditions:
    // - The node must belong to the linked list received
    on in ohn.frst.*nnext

    // Post-conditions:
    // - If the last value of the list is the one received the linked list should be emptied
    (on = ohn.lst && on = ohn.frst) implies orderedRemoveSingleton[on, ohn]
    // - Else the Node received is removed and the nodes that were before and after are connected
    (on != ohn.frst || on != ohn.lst) implies orderedRemoveRest[on, ohn]

    // Frame-conditions:
    // - All the linked lists different from the one received stay the same
    all ohn1: OrderedHeadNode | ohn1 != ohn implies ohn1.frst' = ohn1.frst && ohn1.lst' = ohn1.lst
    // - All the nodes that are not the received one or the next one (it could be none) stay the same
    all on1: OrderedNode | (on1 != on && on1 != on.nnext && on1 != on.nprev) implies on1.nnext' = on1.nnext && on1.nprev' = on1.nprev
}

// assert A {
//     always all on1, on2: OrderedNode, ohn1: OrderedHeadNode | 
//         (on1 = ohn1.frst && on2 = ohn1.lst && on2 != on1) implies some on3: OrderedNode - on2 - on1 | orderedInsert[on3, ohn1]
    
// }

// assert A {
//     some n1: OrderedNode, hn: OrderedHeadNode | n1 !in OrderedHeadNode.frst.*nnext && n1 !in HeadNode.frst.*nnext && #(hn.frst.*nnext) = 3 && hn.frst.*nnext.id in n1.id.nexts[]
// }

// EX 4.2
// run {}
// for exactly 2 OrderedHeadNode, exactly 5 OrderedNode, exactly 5 Id, exactly 0 Node, exactly 0 HeadNode

// EX 4.4:
// - Insert Trace

// check A for 5 but 10 steps

// run {
//     eventually once (some n1: OrderedNode, hn: OrderedHeadNode | #(hn.frst.*nnext) = 3 && hn.frst.id in n1.id.nexts[])
//     eventually once (some n1: OrderedNode, hn: OrderedHeadNode | n1 !in OrderedHeadNode.frst.*nnext && n1 !in HeadNode.frst.*nnext && #(hn.frst.*nnext) = 2 && hn.frst.id in n1.id.nexts[])
//     eventually once (some n1: OrderedNode, hn: OrderedHeadNode | n1 !in OrderedHeadNode.frst.*nnext && FirstGreaterId[n1, hn] = hn.frst.id)
//     eventually once (some n: OrderedNode, hn: OrderedHeadNode | #(hn.frst.*nnext) = 2 && orderedInsert[n, hn])
// }

// for exactly 2 OrderedHeadNode, exactly 5 OrderedNode, exactly 5 Id, exactly 0 Node, exactly 0 HeadNode

// for 5 but 6 steps

run orderedInsert for exactly 2 OrderedHeadNode, exactly 5 OrderedNode, exactly 5 Id, exactly 0 Node, exactly 0 HeadNode

// - Remove Trace
// run orderedRemove for exactly 2 OrderedHeadNode, exactly 5 OrderedNode, exactly 5 Id, exactly 0 Node, exactly 0 HeadNode