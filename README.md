HANDIN: final


OVERVIEW:
- KD-tree data structure implemented i nalloy (run statments for dimensions 1-5)
- < fill in this part with nearest neighbor stuff > 
- please configure kdTree.als with KDTree.thm, and NearestNeighbors.als with NearestNeighbors.thm

DESIGN CHOICES:
For this project, the overarching goal was to provide a user with a better understanding of the construction and usage of k-d trees. To this end, we provide to alloy files to illustrate the construction and subsequent usage of k-d trees. In kdTree.als, a user can find our model of the data structure of k-d trees, and in NearestNeighbors.als a user can find the model of the process of searching for nearest neighbors on a k-d tree.

In building the kdTree in kdTree.als, we found it important to support 'k' dimensions. To achieve this, a user can specify the dimensionality of the tree in the run statement (see the file for examples and further clarifying comments). Additionally, users can specify the number of data nodes they'd like to see in their tree. This allows a user to see how each level of the tree 'splits' the data-space on a different dimension until it eventually gets back to the 0th dimension. We conceive each data node as the median of its own subtree of data (for a given dimension rem[depth, k]). Additionally each data node contains a field for depth, left and right children, its k-arity datatuple, and the dimension it is splitting the data on (splitOn).


In visualizing the nearest neighbors algorithm, we found it important to project this process over states. This allows users to witness the algorithm navigating the kd-tree to find a nearest neighbor which illustrates the usefulness of a well-constructed kd-tree for finding nearest neighbors in k-dimensional data spaces. In addition, it allows use to represent recursive calls in Alloy by adding Nodes to a search list. A node is popped off this search list at each state (if there are nodes in the search list), and checked for if it should be added to the nearest neighbors. It also checks if the children of the node should be recurred upon. If the node's coordinate at the respective axis is less than the target coordinate at that axis, the right child is recurred upon, otherwise the left child is. If the manhattan distance from the furthest node in nearest neighbors is greater than the axis distance of the current node or the nearest neighbors is not full, then the other node is also recurred upon. We faced some challenges in representing a recursive call stack, as when full recursion is used (recur on both children), the nodes must be added to the call stack at the same time due to the abstraction of using pre and post states (both must be present in the call stack of the post state). In actuality, the other node would only be added after fully exploring the first node, however, this was difficult to emulate in the time we had. Therefore we added the first node to the front of call stack and the other node to the back. This imperfect approximation leads to a worse algorithm on trees where there is not a significant difference between the number of nodes and the number of neighbors to search for, or when there is not a significant differences between the dimensions of nodes. Unforunately, both of these cases hold in alloy. 

When asserting the properties of nearest neighbors...


