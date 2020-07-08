package hw2

import (
	"github.com/gonum/graph"

	"math"
)

// Helper Method to determine if Node s is a predecessor to node d in graph g. [O(1)]
func IsPredecessor(g graph.Graph, s graph.Node, d graph.Node, weight Weighting) bool {
	if g.Edge(s, d) != nil {
		return true
	} else {
		return false
	}
}

// Check if there are any forbidden nodes in the graphs acording to bellman-Fords predicate.
// the Forbidden nodes are indicated by overwritting the forbidden input array, which is
// modified by reference.[O(n)]
func CheckForbiddenBF(nodes []graph.Node, path Shortest, weight Weighting, pre [][]bool, forbidden []bool) {
	// Auxiliar signal to wait for all threads
	bf_thread := make(chan bool, len(nodes))
	for _, n := range nodes {
		i := path.indexOf[n.ID()]
		// Spawn threads for the analysis of each individual node, this does a sweep on al nodes( O(n) )
		go func(i int, n graph.Node) {
			forbidden[i] = false
			for _, k := range nodes {
				j := path.indexOf[k.ID()]
				if pre[i][j] {
					w, ok := weight(k, n)
					if !ok {
						panic("bf: unexpected invalid weight")
					}
					// forbidden predicate validation
					if path.dist[path.indexOf[n.ID()]] > (path.dist[path.indexOf[k.ID()]] + w) {
						forbidden[i] = true
						continue
					}
				}
			}
			bf_thread <- false
		}(i, n)
	}
	// Wait for all spawned threads to complete.
	for i := 0; i < len(nodes); i++ {
		<-bf_thread
	}
}

// Helper method to reduce the elements of a boolean array by Or'ing them [O(logn)]
func OrBoolVec(bool_vec []bool) bool {

	local_vec := make([]bool, len(bool_vec))
	it_vec := make([]bool, len(bool_vec))
	// Auxiliar variable for thread synchronization
	thread := make(chan bool, len(bool_vec))
	// Slices in parameters are always sent by reference, so we need to clone
	// it to avoid messing with the original indormation
	copy(local_vec, bool_vec)

	for h := 1; h <= int(math.Ceil(math.Log2(float64(len(bool_vec))))); h++ { // [O(logn)]
		// this method may actually throw off the time complexity??
		copy(it_vec, local_vec)

		for i := 0; i < len(bool_vec); i++ {
			// Spawn threads for comparisons of level h
			go func(i int) { // [ O(1) ]
				if i < int(math.Ceil(float64(len(bool_vec))/math.Exp2(float64(h)))) {
					if 2*i == len(bool_vec)-1 {
						local_vec[i] = it_vec[2*i]
					} else {
						local_vec[i] = it_vec[2*i] || it_vec[2*(i+1)-1]
					}
				}
				thread <- false
			}(i)
		}

		// Wait for al spawned threads to complete
		for i := 0; i < len(bool_vec); i++ {
			<-thread
		}
	}
	return local_vec[0]
}

// Apply the bellman-ford algorihtm to Graph and return
// a shortest path tree.
//
// Note that this uses Shortest to make it easier for you,
// but you can use another struct if that makes more sense
// for the concurrency model you chose.
func BellmanFord(s graph.Node, g graph.Graph) Shortest {

	if !g.Has(s) {
		return Shortest{from: s}
	}
	var weight Weighting
	if wg, ok := g.(graph.Weighter); ok {
		weight = wg.Weight
	} else {
		weight = UniformCost(g)
	}

	nodes := g.Nodes()
	path := newShortestFrom(s, nodes)

	bf_thread := make(chan bool, len(nodes))
	// For simplicity, compute predecesor matrix
	pre := make([][]bool, len(nodes))

	// If two threads panic at the same time, the tester will only recover from one
	// and the second one will complete the panic, stopping the test eexution. For
	// this reason, we compute whether each node has negative edges conected to them
	// in parallel, and combine the results to panic at the end.
	hasNegative := make([]bool, len(nodes))
	for _, n := range nodes {
		i := path.indexOf[n.ID()]

		// Spawn threads to check which nodes preceed others, as well
		// as determine whether a node has negative edges associated with it.
		go func(i int, n graph.Node) {
			// each thread has only one for loop, resulting in O(n)

			pre[i] = make([]bool, len(nodes))

			for _, k := range nodes { // [O(n)]
				j := path.indexOf[k.ID()]
				pre[i][j] = IsPredecessor(g, k, n, weight)

				if pre[i][j] {
					w, ok := weight(k, n)
					if !ok {
						panic("bf: unexpected invalid weight")
					}
					if w < 0 {
						hasNegative[i] = true
					}
				}

			}
			bf_thread <- false
		}(i, n)

	}

	// Wait for all spawned threds to complete.
	for i := 0; i < len(nodes); i++ {
		<-bf_thread
	}

	// If any nodes contain negative edges, panic
	if OrBoolVec(hasNegative) {
		panic("bf: negative edge weight")
	}

	forbidden := make([]bool, len(nodes))

	// Compute initial forbidden nodes
	CheckForbiddenBF(nodes, path, weight, pre, forbidden)
	SomeForbidden := OrBoolVec(forbidden)

	// run algorithm until no forbidden nodes are detected
	for SomeForbidden {

		for i, n := range nodes {

			go func(i int, n graph.Node) {
				if forbidden[i] {
					min := math.Inf(1)
					for j, k := range nodes { // [ O(n) ]
						if pre[i][j] {
							w, ok := weight(k, n)
							if !ok {
								panic("bf: unexpected invalid weight")
							}
							if w < 0 {
								panic("bf: negative edge weight")
							}
							if min > (path.dist[path.indexOf[k.ID()]] + w) {
								min = path.dist[path.indexOf[k.ID()]] + w
								path.set(path.indexOf[n.ID()], min, path.indexOf[k.ID()])
							}
						}
					}
				}
				bf_thread <- false
			}(i, n)

		}

		for i := 0; i < len(nodes); i++ {
			<-bf_thread
		}

		// Update to the new set of forbidden nodes
		CheckForbiddenBF(nodes, path, weight, pre, forbidden)
		SomeForbidden = OrBoolVec(forbidden)
	}
	return path
}

// Helper method to update values in the Shortest variable given the the relaxation criteria.
func relax(d graph.Node, c float64, s graph.Node, path Shortest, delta float64, B map[int]map[graph.Node]bool) {

	if c < path.dist[path.indexOf[d.ID()]] {
		path.set(path.indexOf[d.ID()], c, path.indexOf[s.ID()])
		// if current bucket doesn't exist, create it
		if B[int(c/delta)] == nil {
			B[int(c/delta)] = make(map[graph.Node]bool)
		}
		B[int(c/delta)][d] = true
	}
}

// Apply the delta-stepping algorihtm to Graph and return
// a shortest path tree.
//
// Note that this uses Shortest to make it easier for you,
// but you can use another struct if that makes more sense
// for the concurrency model you chose.
func DeltaStep(s graph.Node, g graph.Graph) Shortest {
	delta := float64(3)
	if !g.Has(s) {
		return Shortest{from: s}
	}
	var weight Weighting
	if wg, ok := g.(graph.Weighter); ok {
		weight = wg.Weight
	} else {
		weight = UniformCost(g)
	}

	nodes := g.Nodes()
	path := newShortestFrom(s, nodes)

	ds_thread := make(chan bool, len(nodes))
	// For simplicity, compute heavy/light matrix
	heavy := make([][]bool, len(nodes))
	light := make([][]bool, len(nodes))

	hasNegative := make([]bool, len(nodes))

	// Compute heavy and light edges on a per node basis [ O(n) ]
	for _, n := range nodes {
		i := path.indexOf[n.ID()]
		go func(i int, n graph.Node) {
			heavy[i] = make([]bool, len(nodes))
			light[i] = make([]bool, len(nodes))
			for _, k := range nodes {
				j := path.indexOf[k.ID()]
				if g.Edge(n, k) != nil {
					w, ok := weight(n, k)
					if !ok {
						panic("delta-step: unexpected invalid weight")
					}
					if w < 0 {
						hasNegative[i] = true
					}
					if w < delta {
						heavy[i][j] = false
						light[i][j] = true
					} else {
						heavy[i][j] = true
						light[i][j] = false
					}
				} else {
					heavy[i][j] = false
					light[i][j] = false
				}
			}
			ds_thread <- false
		}(i, n)
	}
	for i := 0; i < len(nodes); i++ {
		<-ds_thread
	}

	// If any elements have negative edges associated with them, panic [O(logn)]
	if OrBoolVec(hasNegative) {
		panic("delta-step: negative edge weight")
	}

	// This will be our Buckets variable
	B := make(map[int]map[graph.Node]bool)

	// Create first bucket and insert source element into it
	B[0] = make(map[graph.Node]bool)
	B[0][s] = true

	i := 0

	//This loop will execute until all buckets have been deleted.
	for len(B) != 0 {
		S := make(map[graph.Node]bool)
		req := make(map[deltaEdge]bool)
		for B[i] != nil {
			req = make(map[deltaEdge]bool)

			// ds_thread := make(chan bool, len(B[i]))
			for n, _ := range B[i] {

				// go func(n graph.Node) {
				k := path.indexOf[n.ID()]
				for _, v := range g.From(n) {
					j := path.indexOf[v.ID()]
					if light[k][j] {
						w, ok := weight(n, v)
						if !ok {
							panic("delta-step: unexpected invalid weight")
						}
						newCost := w + path.dist[k]
						req[deltaEdge{dest: v, dist: newCost, source: n}] = true
					}
				}
				// ds_thread <- false
				// }(n)

				S[n] = true
			}

			// for i := 0; i < len(B[i]); i++ {
			// 	<-ds_thread
			// }

			delete(B, i)

			// ds_thread := make(chan bool, len(req))
			// Relax all request from light edges in B[i]
			for request, _ := range req {
				// go func(request deltaEdge) {
				relax(request.dest, request.dist, request.source, path, delta, B)
				// ds_thread <- false
				// }(request)
			}

			// for i := 0; i < len(ds_thread); i++ {
			// 	<-ds_thread
			// }

		}

		req = make(map[deltaEdge]bool)

		ds_thread := make(chan bool, len(S))
		for n, _ := range S {
			delete(S, n)
			go func(n graph.Node) {
				k := path.indexOf[n.ID()]
				for _, v := range g.From(n) {
					j := path.indexOf[v.ID()]
					if heavy[k][j] {
						w, ok := weight(n, v)
						if !ok {
							panic("delta-step: unexpected invalid weight")
						}
						newCost := w + path.dist[k]
						req[deltaEdge{dest: v, dist: newCost, source: n}] = true
					}
				}
				ds_thread <- false
			}(n)

		}
		for i := 0; i < len(ds_thread); i++ {
			<-ds_thread
		}

		// Relax all request from heavy edges in S
		ds_thread = make(chan bool, len(req))
		for request, _ := range req {
			go func(request deltaEdge) {
				relax(request.dest, request.dist, request.source, path, delta, B)
				ds_thread <- false
			}(request)
		}

		for i := 0; i < len(ds_thread); i++ {
			<-ds_thread
		}

		// delete the explore bucket
		delete(B, i)
		i++

	}

	return path
}

// Runs dijkstra from gonum to make sure that the tests are correct.
func Dijkstra(s graph.Node, g graph.Graph) Shortest {
	return DijkstraFrom(s, g)
}

type deltaEdge struct {
	dest   graph.Node
	dist   float64
	source graph.Node
}
