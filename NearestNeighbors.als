open util/ordering[State]
open kdTree

one sig Target {
	dimensions: seq Int,
	k: Int
} {
	#dimensions = #Root.dimensions
	k <= #dimensions
	k > 0
}

one sig NearestNeighbors {
	nodes: set Node
}

sig State {
	searching: set Node	
}

sig Event {
	pre: State,
 	post: State
} {
	all n: pre.searching {
		n.dimensions[rem[n.depth, #n.dimensions]] <= Target.dimensions[rem[n.depth, #n.dimensions]] implies {
				n.right in post.searching
		}
		n.dimensions[rem[n.depth, #n.dimensions]] > Target.dimensions[rem[n.depth, #n.dimensions]] implies {
				n.left in post.searching
		}
		n not in post.searching
	}
}

fact trace {
	all state: (State - last) | {
		some e: Event | e.pre = state and e.post = state.next
	}
}


fact initial {
	first.searching = Root
}

fact last {
	no last.searching
}




run{} for exactly 3 Node, 7 Int, 5 State,  4 Event
