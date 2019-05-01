
sig Node {
	left: lone Node,
	right: lone Node,
	parent: lone Node,
	depth: Int,
	dimensions: seq Int
}

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

fact isSorted {
	all n: Node {
		all c: Node | c in n.left.*(left+right) iff {
			// everything on the left subtree
			c.dimensions[rem[n.depth, #n.dimensions]] < n.dimensions[rem[n.depth, #n.dimensions]]
		}
	}
}

fact median {
	all n: Node {
		sub[#n.left.*(left+right), #n.right.*(left+right)] <= 1 and
		sub[#n.left.*(left+right), #n.right.*(left+right)] >= -1
	}
}


pred isChild[n, c: Node] {
	n.left = c or n.right = c
}

pred hasChild[n: Node]  {
	some n.left or some n.right
}

run{} for exactly 4 Node, 7 Int
