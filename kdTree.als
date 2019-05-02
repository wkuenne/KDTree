sig Node {
	left: lone Node,
	right: lone Node,
	depth: Int,
	dimensions: seq Int
} {
//what does this mean? does this mean we're using positive integers for our dimensions?
	all i: dimensions.Int | {
		abs[dimensions[i]] > 0
	}
}

lone sig Root extends Node {}


//also good as fact, need data of the same dimension
fact dimensionsMatch {
	#Root.dimensions > 0
	all n: Node | {
		#n.dimensions = #Root.dimensions
	}
}

//good as a fact, makes sense
fact rooted {
  all n: Node-Root | {
      n in Root.^(left + right)
    }
}


//make check
//fact acyclic {
//    all n: Node | n not in n.^(left + right)
//}


//make check
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

//rephrase to make easier to make other things checks
fact isSorted {
	all p: Node { //p for parent, c for children
		all c: Node - n | c.dimensions[rem[p.depth, #p.dimensions]] < p.dimensions[rem[p.depth, #p.dimensions]] implies
			c in p.^left and
			c.dimensions[rem[p.depth, #p.dimensions]] >= p.dimensions[rem[p.depth, #p.dimensions]] implies
			c in p.^right
	}
}


/*checks to: DO NOT ERASE!
- that no node is its own child
- that the tree is acyclic
- that each parent of a subtree is the median of all the data in that tree
-

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

//make check
//fact median {
//	all n: Node {
//		abs[sub[#n.left.*(left+right), #n.right.*(left+right)]] <= 1
//	}
//}


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

run{} for exactly 5 Node, 6 Int


//why is this running so fucking slow? I think isSorted is messed up
