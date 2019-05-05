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

lone sig Root extends Node {}


/* must have all the data be of the same dimension otherwise you won't
be able to build a KD tree from it */
fact dimensionsMatch {
	#Root.dimensions = 2
	all n: Node | {
		#n.dimensions = #Root.dimensions
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
} for exactly 7 Node, 5 Int

/*checks that there are no cycles in the tree*/
check acyclic {
    all n: Node | n not in n.^(left + right)
} for exactly 7 Node, 5 Int

/*checks that the dimension being used at each depth is depth % k, where k is the dimension of the data*/
check splitAtSameDimensionForAGivenDepth {
	all a, b : Node | a.depth = b.depth implies a.splitOn = b.splitOn
} for exactly 7 Node, 5 Int

/*checks that the dimension being split on is depth % dimensions*/
check splitOnConsistent {
	all n : Node | n.splitOn = rem[n.depth, #Root.dimensions]
}


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

run{} for exactly 7 Node, 5 Int
