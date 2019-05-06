open util/ordering[State]
open kdTree

one sig Target {
	dimensions: seq Int,
	k: Int
} {
	#dimensions = #Root.dimensions
	k = 3
	k > 0
	all i: dimensions.Int | {
		dimensions[i] > -8 and dimensions[i] < 8
	}
}

sig State {
	searching: seq Node,
	nearestNeighbors: set Node
}

sig Event {
	pre: State,
 	post: State
} {
	some pre.searching implies {
		addNeighbor[pre, post, pre.searching.first]
	} else {
		post.nearestNeighbors = pre.nearestNeighbors
	}
	lessThanAxis[pre.searching.first, rem[pre.searching.first.depth, #Root.dimensions]] implies {
		recurseOnOtherSubtree[pre, pre.searching.first, rem[pre.searching.first.depth, #Root.dimensions]] implies {
			post.searching = pre.searching.setAt[0, pre.searching.first.right].add[pre.searching.first.left]
		} else {
			post.searching = pre.searching.setAt[0, pre.searching.first.right]
		}
	} else {
		recurseOnOtherSubtree[pre, pre.searching.first, rem[pre.searching.first.depth, #Root.dimensions]] implies {
			post.searching = pre.searching.setAt[0, pre.searching.first.left].add[pre.searching.first.right]
		} else {
			post.searching = pre.searching.rest.setAt[0, pre.searching.first.left]
		}
	}
}

//pred leftRecursion[pre, post: State, index: Int] {
//		recurseOnOtherSubtree[post, index] implies {
//			post.searching = pre.searching.rest.add[pre.searching.first.left].add[pre.searching.first.right]
//		} else {
//			post.searching = pre.searching.rest.add[pre.searching.first.left]
//		}
// }


pred recurseOnOtherSubtree[pre: State, search: Node, index: Int] {
	notFullNeighbors[pre] or some max: pre.nearestNeighbors | {
		all n: pre.nearestNeighbors | {
			max.dimensions[index] >= n.dimensions[index]
		}
		manhattanDist[max.dimensions, Target.dimensions] > axisDist[search.dimensions, Target.dimensions, index]
	}
}

pred addNeighbor[pre, post: State, new: Node] {
	notFullNeighbors[pre] implies { 
		post.nearestNeighbors = pre.nearestNeighbors + new
	} else {
		replaceMax[pre, post, new]
	}
}

fact trace {
	all state: (State - last) | {
		some e: Event | e.pre = state and e.post = state.next
	}
}

pred lessThanAxis[n: Node, axis: Int] {
	n.dimensions[axis] <=	Target.dimensions[axis]
}

pred notFullNeighbors[state: State] {
	#state.nearestNeighbors < Target.k
}

fact initial {
	first.searching.first = Root
	#first.searching = 1
	no first.nearestNeighbors
}

fact last {
	//no last.searching
}

//new is pre.searching.first
//predicate that returns true if m is the index of the maximum value in sequence 
pred replaceMax[pre, post: State, search: Node] { 
	some max: pre.nearestNeighbors | {
		all node: pre.nearestNeighbors | {
			manhattanDist[max.dimensions, Target.dimensions] >= 
			manhattanDist[node.dimensions, Target.dimensions] 
		}
 		manhattanDist[max.dimensions, Target.dimensions] > 
		manhattanDist[search.dimensions, Target.dimensions] implies {
			post.nearestNeighbors = pre.nearestNeighbors - max + search
		} else {
			post.nearestNeighbors = pre.nearestNeighbors
		}
	}
}

fun axisDist[s1, s2: seq Int, axis: Int] : Int {
	abs[sub[s1[axis], s2[axis]]]
}

fun manhattanDist[s1, s2: seq Int] : Int {
	sum i: s1.Int | abs[sub[s1[i], s2[i]]]
}

run{} for exactly 7 Node, 6 Int, 9 State, 8 Event
