sig Node {
	left: lone Node,
	right: lone Node,
	parent: lone Node,
	depth: Int,
	dimensions: seq Int,
//	aligned: Int //this is whatever dimension the node is splitting the space on (ie 0 to k-1)
}
// {
//	aligned =
//check that all aligned are in this range, check that each subsequent aligned is correct (+1 or back to 0)
//}

lone sig Root extends Node {}

fact dimensionsMatch {
	#Root.dimensions > 0
	all n: Node | {
		#n.dimensions = #Root.dimensions
	}
}

fact rooted {
  all n: Node-Root | {
      n in Root.^(left + right)
    }
}

	
fact acyclic {
    all n: Node | n not in n.^(left + right)
}
   
fact loneParent {
	all n: Node | {
		no n.right & n.left
		lone (left+right).n
	}
}

fact parents {
	no Root.parent
	all n: Node | all c: Node {
		 isChild[n, c] implies c.parent = n
	}
}

fact depths {
	all n: Node-Root | {
		n.depth = add[n.parent.depth, 1]
	}
	Root.depth = 0
}

//consolidate these into a single tree properties fact?

//this should be an assert
//fact completeness {
//	all n: Node | all c: Node | {
//		isChild[n, c] and hasChild[c] implies one n.left and one n.right
//	}
//}

fact isSorted {
	all n: Node {
		all c: Node | c in n.left.*(left+right)  iff  {
			// everything on the left subtree
			c.dimensions[rem[n.depth, #n.dimensions]] < c.dimensions[rem[n.depth, #n.dimensions]]
		}
	}

	all n: Node {
		all c: Node | c in n.left.*(left+right)  iff  {
			// everything on the left subtree
			c.dimensions[rem[n.depth, #n.dimensions]] < c.dimensions[rem[n.depth, #n.dimensions]]
		}
	}

//	all n: Node | n in Root.right.*(left+right) iff {
//		// everything on the right subtree
//		n.dimensions[0] >= Root.dimensions[0]
//	}
}

pred isChild[n, c: Node] {
	n.left = c or n.right = c
}

pred hasChild[n: Node]  {
	some n.left or some n.right
}

run{} for exactly 3 Node, 7 Int
