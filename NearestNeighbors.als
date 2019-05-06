open util/ordering[State]
open kdTree

one sig Target {
	dimensions: seq Int,
	k: Int
} {
	#dimensions = #Root.dimensions
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
	// if it the current node is less than the target node on the axis then recur on 
	// right subtree, otherwise recur on the left
	lessThanAxis[pre.searching.first, pre.searching.first.splitOn] implies {
			// full recursion means recur on both left and right child
			recurseOnOtherSubtree[pre, pre.searching.first, pre.searching.first.splitOn] implies {
				fullRecurse[pre, post, pre.searching.first.right, pre.searching.first.left]
			} else {
				// recur on just the right child
				baseRecurse[pre, post, pre.searching.first.right]
			}
	} else {
			// full recursion means recur on both left and right child
			recurseOnOtherSubtree[pre, pre.searching.first, pre.searching.first.splitOn] implies {
				fullRecurse[pre, post, pre.searching.first.left, pre.searching.first.right]
			} else {
				// recur on only the left child
				baseRecurse[pre, post, pre.searching.first.left]
			}
	}
}

pred fullRecurse[pre, post: State, first, last: Node] {
	some first implies {
		post.searching = pre.searching.rest.insert[0, first].add[last]
	} else {
		post.searching = pre.searching.rest.add[last]
	}	
}

pred baseRecurse[pre, post: State, node: Node] {
	some node implies {
		post.searching = pre.searching.rest.insert[0, node]
	} else {
		post.searching = pre.searching.rest
	}
}

// checks whether both the left and right child should be recurred upon by 
// checking the manhattan dist from the node checked to the target and comparing
// it to the distance on the respective axis. If this holds, or the neighbors is not full, 
// then recur upon both children
pred recurseOnOtherSubtree[pre: State, search: Node, index: Int] {
	notFullNeighbors[pre] or some max: pre.nearestNeighbors | {
		all n: pre.nearestNeighbors | {
			max.dimensions[index] >= n.dimensions[index]
		}
		manhattanDist[max.dimensions, Target.dimensions] > axisDist[search.dimensions, Target.dimensions, index]
	}
}

// predicate for adding a neighbor to nearest neighbors
pred addNeighbor[pre, post: State, new: Node] {
	// if nearest neighbors is not full then add it
	notFullNeighbors[pre] implies { 
		post.nearestNeighbors = pre.nearestNeighbors + new
	} else {
		// replace the max otherwise
		replaceMax[pre, post, new]
	}
}

// finds the max node in the nearest neighbors of pre, replaces it in post with the 
// search node if it is greater than the search node
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

// begin with only the root in searching with an empty nearest neighbors
fact initial {
	first.searching.first = Root
	first.searching.last = Root
	no first.nearestNeighbors
}

fact last {
	no last.searching
}

// calculates the axis distance between two sequences
fun axisDist[s1, s2: seq Int, axis: Int] : Int {
	abs[sub[s1[axis], s2[axis]]]
}

// calculates the manhattan distance between two nodes
fun manhattanDist[s1, s2: seq Int] : Int {
	sum i: s1.Int | abs[sub[s1[i], s2[i]]]
}

check sizeOfNeighbors {
	Target.k < #Node implies {
		#last.nearestNeighbors = Target.k 
	} else { 
		#last.nearestNeighbors = #Node
	}
} for exactly 7 Node, 5 Int, exactly 3 Dimension, exactly 8 State, exactly 7 Event

check neighborsAreClosest {
	all node: Node - last.nearestNeighbors | {
		all neighbor: last.nearestNeighbors | {
			manhattanDist[node.dimensions, Target.dimensions] >= 
			manhattanDist[neighbor.dimensions, Target.dimensions]
		}
	}
} for exactly 7 Node, 5 Int, exactly 2 Dimension, exactly 8 State, exactly 7 Event

run{} for exactly 7 Node, 5 Int, exactly 3 Dimension, 8 State, 7 Event
run{} for exactly 7 Node, 5 Int, exactly 2 Dimension, 8 State, 7 Event
run{} for exactly 7 Node, 5 Int, exactly 1 Dimension, 8 State, 7 Event

