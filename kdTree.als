one sig KDTree {
	dimensions: Int
}

sig Node {
	left: lone Node,
	right: lone Node,
	parent: lone Node,
	depth: Int,
	dimensions: seq Int
}

lone sig Root extends Node {}

fact dimensionsMatch {
	KDTree.dimensions = 4
	all n: Node | {
		#n.dimensions = KDTree.dimensions
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

//fact completeness {
//	all n: Node | all c: Node | {
//		isChild[n, c] and hasChild[c] implies one n.left and one n.right
//	}
//}

fact isKDRacist {
	all n: Node | {
		//TODO modulo//
		//n.right.*(left + right).dimensions[n.depth] > n.dimensions[n.depth]
		//n.left.*(left + right).dimensions[n.depth] < n.dimensions[n.depth]
		all c: Node | {
			c in n.left.*(left + right) iff c.dimensions[n.depth] < n.dimensions[n.depth]
		}
	}
}

pred isChild[n, c: Node] {
	n.left = c or n.right = c
}

pred hasChild[n: Node]  {
	some n.left or some n.right
}

run{} for exactly 5 Node, 7 Int
