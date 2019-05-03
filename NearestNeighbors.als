open util/ordering[State]
open kdTree

one sig Target {
	dimensions: seq Int,
	k: Int
} {
	#dimensions = #Root.dimensions
	k <= 2
	k > 0
}

sig State {
	searching: seq Node,
	nearestNeighbors: set Node
}

sig Event {
	pre: State,
 	post: State
} {
	notFullNeighbors[pre.nearestNeighbors] implies {
		post.nearestNeighbors = pre.nearestNeighbors + pre.searching.first
	} else {
		post.nearestNeighbors = pre.nearestNeighbors
	}
	lessThanAxis[pre.searching.first] implies {
			leftRecursion[pre, post]
	} else {
		notFullNeighbors[post.nearestNeighbors] implies {
				post.searching = pre.searching.rest.add[pre.searching.first.right].add[pre.searching.first.left]
		} else {
			post.searching = pre.searching.rest.add[pre.searching.first.right]
		}
	}
}

pred leftRecursion[pre, post: State] {
		notFullNeighbors[post.nearestNeighbors] implies {
			post.searching = pre.searching.rest.add[pre.searching.first.right].add[pre.searching.first.left]
		} else {
			post.searching = pre.searching.rest.add[pre.searching.first.right]
		}
}

pred checkRightFromLeft[state: State, index: Int] {
	lone max: state.nearestNeighbors | {
		all n: state.nearestNeighbors | {
			max.dimensions[index] >= n.dimensions[index]
		}
		manhattanDist[max.dimensions, Target.dimensions] > axisDist[max.dimensions, Target.dimensions, index]
	}
}

fact trace {
	all state: (State - last) | {
		some e: Event | e.pre = state and e.post = state.next
	}
}

pred lessThanAxis[n: Node] {
	n.dimensions[rem[n.depth, #Root.dimensions]] <=	Target.dimensions[rem[n.depth, #Root.dimensions]]
}

pred notFullNeighbors[nearestNeighbors: set Node] {
	#nearestNeighbors < Target.k
}

fact initial {
	first.searching.first = Root
	#first.searching = 1
	no first.nearestNeighbors
}

fact last {
	no last.searching
}

//TODO don't use this
fun axisDist[s1, s2: seq Int, axis: Int] : Int {
	abs[sub[s1[axis], s2[axis]]]
}

fun manhattanDist[s1, s2: seq Int] : Int {
	sum i: s1.Int | abs[sub[s1[i], s2[i]]]
}

run{} for exactly 4 Node, 6 Int, 4 State, 3 Event
