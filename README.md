HANDIN: final


OVERVIEW:
- KD-tree data structure implemented i nalloy (run statments for dimensions 1-5)
- < fill in this part with nearest neighbor stuff > 
- please configure kdTree.als with KDTree.thm, and NearestNeighbors.als with NearestNeighbors.thm

DESIGN CHOICES:
For this project, the overarching goal was to provide a user with a better understanding of the construction and usage of k-d trees. To this end, we provide to alloy files to illustrate the construction and subsequent usage of k-d trees. In kdTree.als, a user can find our model of the data structure of k-d trees, and in NearestNeighbors.als a user can find the model of the process of searching for nearest neighbors on a k-d tree.

In building the kdTree in kdTree.als, we found it important to support 'k' dimensions. To achieve this, a user can specify the dimensionality of the tree in the run statement (see the file for examples and further clarifying comments). Additionally, users can specify the number of data nodes they'd like to see in their tree. This allows a user to see how each level of the tree 'splits' the data-space on a different dimension until it eventually gets back to the 0th dimension. We conceive each data node as the median of its own subtree of data (for a given dimension rem[depth, k]). Additionally each data node contains a field for depth, left and right children, its k-arity datatuple, and the dimension it is splitting the data on (splitOn).


In visualizing the nearest neighbors algorithm, we found it important to project this process over states. This allows users to witness the algorithm navigating the kd-tree to find a nearest neighbor which illustrates the usefulness of a well-constructed kd-tree for finding nearest neighbors in k-dimensional data spaces. < add more hear about the nearest neighbor design choices >

CONCLUSIONS:
yeah Idk what to write here yet. we should meet and go over it.
