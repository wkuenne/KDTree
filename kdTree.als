one sig KDtree {
	dim : set Int,
	nodes: set Node
} {
	one dim
	dim = 2
}

sig Node {
	lchild: lone Node,
	rchild: lone Node	
}

fact treeProps {
	no n: Node | n not in KDtree.nodes
	all n: Node | n not in n.^(rchild) and n not in n.^(lchild)
	no n: Node | n in n.^(rchild) + n.^(lchild)
}


run {} for 7 int, exactly 6 Node
