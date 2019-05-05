sig Node {
	left: lone Node,
	right: lone Node,
	depth: Int,
	splitOn: Int,
	dimensions: seq Int
} {
	/*this makes the code run faster because data only runs between -8 to 8*/
	all i: dimensions.Int | {
		abs[dimensions[i]] <= 8
	}
	this not in left and this not in right //no node is its own child
}

/*used in run statment to choose k-dimensional space for data*/
sig Dimension {}

lone sig Root extends Node { 
	k: Int
} {
	k = #Dimension
}


/* must have all the data be of the same dimension otherwise you won't
be able to build a KD tree from it */
fact dimensionsMatch {
//	#Root.dimensions = 5
	all n: Node | {
		#n.dimensions = Root.k
	}
}

/* must have all data nodes in the tree which means they are all in
 the transitive closure of the children of the root */
fact rooted {
  all n: Node-Root | {
      n in Root.^(left + right)
    }
}

/*all nodes have at most one parent */
fact loneParent {
	all n: Node | {
		no n.right & n.left
		lone (left+right).n
	}
}

/*root depth is 0 and all other nodes depth are there parents  + 1. all nodes are split on
depth % k, where k is the arity of the data (ie the data is k-dimensional*/
fact depths {
	// k = #Root.dimensions
	all n: Node-Root | {
		n.depth = add[n.~(left+right).depth, 1]
		n.splitOn = rem[n.depth, #Root.dimensions]
	}
	Root.depth = 0
	Root.splitOn = rem[Root.depth, #Root.dimensions]
}

/*process of building the tree from data nodes*/
fact sort {
	all p: Node { //p for parent, c for children
		//p is the median <--doesn't make it be the median <-- verified in a check
		abs[sub[#p.left.*(left+right), #p.right.*(left+right)]] <= 1
		//all the children are sorted
		all c: p.^(left + right) | c.dimensions[rem[p.depth, #p.dimensions]] < p.dimensions[rem[p.depth, #p.dimensions]] implies
			c in p.left.*(left+right) else
			c in p.right.*(left+right)
	}
}

/*every node is the median of its own subtree. Verify this by showing that for every node n, the number of nodes with data values 
less than n's at the given dimension is equal (or off by 1) to the number of nodes with data values greater than or equal to n's at the
given dimension. Essentially shows that n is the true median of the dataset of a given subtree*/
check median {
	all n: Node {
		abs[sub[#{c : n.^(left + right) | c.dimensions[rem[n.depth, #n.dimensions]] < n.dimensions[rem[n.depth, #n.dimensions]]},
				#{c : n.^(left + right) | c.dimensions[rem[n.depth, #n.dimensions]] >= n.dimensions[rem[n.depth, #n.dimensions]]}]] <= 1
	}
} for exactly 7 Node, 5 Int, 3 Dimension

/*checks that for each node, there is no data in its left subtree that is greater than the node at that dimension,
and that there is no data in its right subtree that is  less than the node at that dimension*/
check sortedRight {
	all a: Node {
		no b: a.left.*(left+right) | b.dimensions[rem[a.depth, #a.dimensions]] >= a.dimensions[rem[a.depth, #a.dimensions]]
		no b: a.right.*(left+right) | b.dimensions[rem[a.depth, #a.dimensions]]  < a.dimensions[rem[a.depth, #a.dimensions]]
	}
} for exactly 7 Node, 5 Int, 3 Dimension

/*checks that there are no cycles in the tree*/
check acyclic {
    all n: Node | n not in n.^(left + right)
} for exactly 7 Node, 5 Int, 3 Dimension

/*checks that the dimension being used at each depth is depth % k, where k is the dimension of the data*/
check splitAtSameDimensionForAGivenDepth {
	all a, b : Node | a.depth = b.depth implies a.splitOn = b.splitOn
} for exactly 7 Node, 5 Int, 3 Dimension

/*checks that the dimension being split on is depth % dimensions*/
check splitOnConsistent {
	all n : Node | n.splitOn = rem[n.depth, #Root.dimensions]
} for exactly 7 Node, 5 Int, 3 Dimension

/*checks that the user's chosen dimension is consistently the arity of all the data*/
check dimensionsMatch {
	no a,b : Node | #a.dimensions != #b.dimensions //make a check
	all n: Node | #n.dimensions = Root.k
} for exactly 7 Node, 5 Int, 3 Dimension


/*absolute value function */
fun abs[n: Int] : n {
	n < 0 implies sub[0, n] else n
}

/*tree ADT function*/
pred isChild[n, c: Node] {
	n.left = c or n.right = c
}

/*tree ADT function*/
pred hasChild[n: Node]  {
	some n.left or some n.right
}

/*a perfect binary tree has 2^h+1 - 1 nodes, where h is the zero-indexed height of the tree.*/
/*if the user want a k-dimension above 4, they need to specify k seq in the run statement to accomodate it*/
run{} for exactly 12 Node, 5 Int, exactly 5 Dimension, 5 seq
run{} for exactly 12 Node, 5 Int, exactly 4 Dimension
run{} for exactly 12 Node, 5 Int, exactly 3 Dimension
run{} for exactly 7 Node, 5 Int, exactly 2 Dimension
run{} for exactly 7 Node, 5 Int, exactly 1 Dimension
