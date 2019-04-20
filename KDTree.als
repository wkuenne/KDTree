sig Node {
	left, right, parent: Node,
	dimensions: seq Int
}

fact dimensionsMatchK {
	#Node.dimensions = 4
	
}

run {} for 1 Node
