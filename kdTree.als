sig Node {
	left: lone Node,
	right: lone Node
}

fact rooted {
      some r: Node | all n: Node-r | {
          n in r.^(left + right)
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

run{} for exactly 4 Node
