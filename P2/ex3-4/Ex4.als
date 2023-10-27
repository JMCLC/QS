open Ex3
open util/ordering[Id]

sig OrderedHeadNode extends HeadNode {
}

sig OrderedNode extends Node {
    id: one Id
}

sig Id {}

// C12: An Id must always have a different Ordered Node
fact C12 {
    always all id1: Id | #(id1.~id) = 1 
}

// C13: For all Ordered Nodes that belong to the same Linked List the previous one as an Id smaller than the next one
fact C13 {
    always all on1, on2: OrderedNode | on2 in on1.^nnext implies on1.id.lt[on2.id]
}

pred orderedInsertSingleton[on: OrderedNode, ohn: OrderedHeadNode] {
    // Post-conditions:
    ohn.frst' = on
    ohn.lst' = on
    no (on.nprev')
    no (on.nnext')

    // Frame-conditions:
    // - All the nodes that are not the received one stay the same
    all on1: OrderedNode - on | on1.nnext' = on1.nnext && on1.nprev' = on1.nprev
}

pred orderedInsertStart[on: OrderedNode, ohn: OrderedHeadNode] {
    // Post-conditions:
    ohn.frst' = on
    ohn.frst.nprev' = on
    on.nnext' = ohn.frst
    no (on.nprev')

    // Frame-conditions:
    // - All the nodes that are not the received one and the first stay the same
    all on1: OrderedNode - on - ohn.frst | on1.nnext' = on1.nnext && on1.nprev' = on1.nprev
}

pred orderedInsertEnd[on: OrderedNode, ohn: OrderedHeadNode] {
    // Post-conditions:
    ohn.lst' = on
    ohn.lst.nnext' = on
    on.nprev' = ohn.lst
    no (on.nnext')

    // Frame-conditions:
    // - All the nodes that are not the received one and the last stay the same
    all on1: OrderedNode - on - ohn.lst | on1.nnext' = on1.nnext && on1.nprev' = on1.nprev
}

pred orderedInsertRest[on: OrderedNode, ohn: OrderedHeadNode] {
    // Post-conditions:
    // - There exists 2 nodes that are connected that the previous one as an id lesser than the node reiceved and the next has a greater one
    all on1, on2: OrderedNode | (on1 in ohn.frst.*nnext && on2 = on1.nnext) && (on.id.gt[on1.id] && on.id.lt[on2.id]) implies 
    on.nprev' = on1 && on.nnext' = on2 && on1.nnext' = on && on2.nprev' = on

    // Frame-conditions:
    // - All nodes that are not these 3 stay the same
    all on1, on2: OrderedNode | (on1 in ohn.frst.*nnext && on2 = on1.nnext) && (on.id.gt[on1.id] && on.id.lt[on2.id]) implies
    all on3: (OrderedNode - on1 - on2 - on) | on3.nnext' = on3.nnext && on3.nprev' = on3.nprev
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
    // - Else if the node has an id less than the first of the list it gets put at the start
    on.id.lt[ohn.frst.id] implies orderedInsertStart[on, ohn]
    // - Else if the node has an id greater than the last of the list it gets put at the end
    on.id.gt[ohn.lst.id] implies orderedInsertEnd[on, ohn]
    // - Else
    ohn.frst != none implies orderedInsertRest[on, ohn]

    // Frame-conditions:
    // - All the linked lists different from the one received stay the same
    all ohn1: OrderedHeadNode - ohn | ohn1.frst' = ohn1.frst && ohn1.lst' = ohn1.lst
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

// EX 4.2
run {}
for exactly 2 OrderedHeadNode, exactly 5 OrderedNode, exactly 5 Id, exactly 0 Node, exactly 0 HeadNode

// EX 4.4:
// - Insert Trace
run orderedInsert for exactly 2 OrderedHeadNode, exactly 5 OrderedNode, exactly 5 Id, exactly 0 Node, exactly 0 HeadNode

// - Remove Trace
run orderedRemove for exactly 2 OrderedHeadNode, exactly 5 OrderedNode, exactly 5 Id, exactly 0 Node, exactly 0 HeadNode