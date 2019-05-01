open util/ordering[State]
open kdTree

one sig Target {
	coords: seq Int,
	k: Int
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
	post.searching = pre.searching.(left + right) - pre.searching
}

fact trace {
	all state: (State - last) | {
		some e: Event | e.pre = state and e.post = state.next
	}
}

fact targetMatches {
	#coords = #Root.dimensions
}

fact initial {
	first.searching = Root
}

fact last {
	no last.searching
}




run{} for exactly 2 Node, 7 Int, 5 State,  4 Event
