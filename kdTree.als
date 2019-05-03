sig Node {
	left: lone Node,
	right: lone Node,
	depth: Int,
	dimensions: seq Int
} {
	//does this mean no zero is mapped to by any dimension?
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

//how does this work? make check
fact loneParent {
	all n: Node | {
		no n.right & n.left
		lone (left+right).n
	}
}

//we could just define the depth as the parent's depth + 1 if we wanted to include a parent field for a node
fact depths {
	all n: Node-Root | {
		n.depth = add[n.~(left+right).depth, 1]
	}
	Root.depth = 0
}

//renamed sort because it's a process
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


/*checks to: DO NOT ERASE!
- that no node is its own child <-- made a fact of the nodes
- that the tree is acyclic <-- checked
- that each parent of a subtree is the median of all the data in that subtree <-- see below
- that it isSorted <-- checked by every node being the median of its subtree for a given dimension
*/

//
//fact isSorted {
//	all n: Node {
//		all c: Node | c in n.left.*(left+right) iff {
//			// everything on the left subtree
//			c.dimensions[rem[n.depth, #n.dimensions]] < n.dimensions[rem[n.depth, #n.dimensions]]
//		}
//	}
//}

/*every node is the median of its own subtree. Verify this by showing that for every node n, the number of nodes with data values 
less than n's at the given dimension is equal (or off by 1) to the number of nodes with data values greater than or equal to n's at the
given dimension. Essentially shows that n is the true median of the dataset of a given subtree*/
check median {
	all n: Node {
		abs[sub[#{c : n.^(left + right) | c.dimensions[rem[n.depth, #n.dimensions]] < n.dimensions[rem[n.depth, #n.dimensions]]},
				#{c : n.^(left + right) | c.dimensions[rem[n.depth, #n.dimensions]] >= n.dimensions[rem[n.depth, #n.dimensions]]}]] <= 1
	}
} for exactly 5 Node, 6 Int

/*checks that there are no cycles in the tree*/
check acyclic {
    all n: Node | n not in n.^(left + right)
} for exactly 5 Node, 6 Int



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

//could write a median function?

run{} for exactly 7 Node, 5 Int


//why is this running so fucking slow? I think isSorted is messed up
//ok it's running faster now. it takes a long time to run the median check, but
// good istances are produced quickly and the acyclic check is fast
