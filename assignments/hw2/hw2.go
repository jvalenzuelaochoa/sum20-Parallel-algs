package hw2

import (
	"container/heap"

	"github.com/gonum/graph"

	"fmt"
	"math"
	"strconv"
)

func IsPredecessor(g graph.Graph, s graph.Node, d graph.Node) bool {
	if g.Edge(s, d) != nil {
		println("detected edge from " + strconv.Itoa(s.ID()) + " to " + strconv.Itoa(d.ID()))
		return true
	} else {
		return false
	}
}

func CheckForbiddenBF(nodes []graph.Node, path Shortest, weight Weighting, pre [][]bool, forbidden []bool) {
	fmt.Println(nodes)
	println("Looking For Forbidden Nodes...")
	for _, n := range nodes {
		i := path.indexOf[n.ID()]
		forbidden[i] = false
		for _, k := range nodes {
			j := path.indexOf[k.ID()]
			if pre[i][j] {
				println("Analyzing edge from " + strconv.Itoa(k.ID()) + " to " + strconv.Itoa(n.ID()))
				w, ok := weight(k, n)
				if !ok {
					panic("bf: unexpected invalid weight")
				}
				if w < 0 {
					panic("delta-step: negative edge weight")
				}
				if path.dist[path.indexOf[n.ID()]] > (path.dist[path.indexOf[k.ID()]] + w) {
					distTon := strconv.FormatFloat(path.dist[path.indexOf[n.ID()]], 'f', -1, 64)
					println(strconv.Itoa(path.indexOf[n.ID()]) + " is forbidden: " + distTon)
					forbidden[i] = true
					continue
				}
			}
		}
	}
}

func OrBoolVec(forb_vec []bool) bool {
	local_vec := make([]bool, len(forb_vec))
	result := make(chan int, len(forb_vec))
	copy(local_vec, forb_vec)
	for h := 1; h <= int(math.Ceil(math.Log2(float64(len(forb_vec))))); h++ {
		for i := 0; i < len(forb_vec); i++ {
			go func(i int) {
				if i < len(forb_vec)/int(math.Ceil(math.Exp2(float64(h)))) {
					if 2*i == len(forb_vec)-1 {
						local_vec[i] = local_vec[2*1]
					} else {
						local_vec[i] = local_vec[2*i] || local_vec[2*(i+1)-1]
					}
				}
				result <- i
			}(i)
		}
		for i := 0; i < len(forb_vec); i++ {
			<-result
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

	result := make(chan int, len(nodes))
	// For simplicity, compute predecesor matrix
	pre := make([][]bool, len(nodes))

	println("Starting Analysis...")
	for _, n := range nodes {
		i := path.indexOf[n.ID()]
		go func(i int, n graph.Node) {
			pre[i] = make([]bool, len(nodes))
			for _, k := range nodes {
				j := path.indexOf[k.ID()]
				pre[i][j] = IsPredecessor(g, k, n)
			}
			result <- i
		}(i, n)

	}
	for i := 0; i < len(nodes); i++ {
		<-result
	}

	forbidden := make([]bool, len(nodes))
	CheckForbiddenBF(nodes, path, weight, pre, forbidden)

	SomeForbidden := false
	if SomeForbidden = OrBoolVec(forbidden); SomeForbidden {
		println("Forbidden nodes detected")
	}
	for SomeForbidden {
		for i, n := range nodes {

			go func(i int, n graph.Node) {
				if forbidden[i] {
					min := math.Inf(1)
					for j, k := range nodes {
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
								println("Overwrite distance to node " + strconv.Itoa(n.ID()) + " to " + strconv.FormatFloat(min, 'f', -1, 64))
								path.set(path.indexOf[n.ID()], min, path.indexOf[k.ID()])
								println(strconv.FormatFloat(path.dist[path.indexOf[n.ID()]], 'f', -1, 64))
							}
						}
					}
				}
				result <- i
			}(i, n)

		}

		for i := 0; i < len(nodes); i++ {
			<-result
		}

		CheckForbiddenBF(nodes, path, weight, pre, forbidden)

		if SomeForbidden = OrBoolVec(forbidden); SomeForbidden {
			println("Forbidden nodes detected")
		}
	}
	return path
}

func relax(d graph.Node, c float64, s int, path Shortest, delta float64, B map[int]*priorityQueue) {
	if c < path.dist[path.indexOf[d.ID()]] {
		fmt.Println("Relaxing node " + strconv.Itoa(d.ID()))
		path.set(path.indexOf[d.ID()], c, s)
		if B[int(c/delta)] == nil {
			fmt.Println("Created bucket: " + strconv.Itoa(int(c/delta)))
			B[int(c/delta)] = &priorityQueue{}
		}
		heap.Push(B[int(c/delta)], distanceNode{node: d, dist: c})
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

	result := make(chan int, len(nodes))
	// For simplicity, compute heavy/light matrix
	heavy := make([][]bool, len(nodes))
	light := make([][]bool, len(nodes))

	hasNegative := make([]bool, len(nodes))

	for _, n := range nodes {
		i := path.indexOf[n.ID()]
		go func(i int, n graph.Node) {
			heavy[i] = make([]bool, len(nodes))
			light[i] = make([]bool, len(nodes))
			for _, k := range nodes {
				j := path.indexOf[k.ID()]
				if g.Edge(n, k) != nil {
					// println("detected edge from " + strconv.Itoa(n.ID()) + " to " + strconv.Itoa(k.ID()))
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
			result <- i
		}(i, n)
	}
	for i := 0; i < len(nodes); i++ {
		<-result
	}

	if OrBoolVec(hasNegative) {
		panic("delta-step: negative edge weight")
	}

	B := make(map[int]*priorityQueue)

	B[0] = &priorityQueue{}

	heap.Push(B[0], distanceNode{node: s, dist: 0})

	i := 0
	for len(B) != 0 {
		fmt.Println("Checking bucket " + strconv.Itoa(i))
		S := priorityQueue{}
		req := deltaQueue{}
		fmt.Println(B[i].Len())
		for B[i].Len() != 0 {
			req = deltaQueue{}
			for B[i].Len() != 0 {
				n := heap.Pop(B[i]).(distanceNode).node
				k := path.indexOf[n.ID()]
				for _, v := range g.From(n) {
					j := path.indexOf[v.ID()]
					if light[k][j] {
						w, ok := weight(n, v)
						if !ok {
							panic("delta-step: unexpected invalid weight")
						}
						newCost := w + path.dist[k]
						heap.Push(&req, deltaEdge{dest: v, dist: newCost, source: n})
					}
				}

				heap.Push(&S, distanceNode{node: n, dist: 0})
			}

			for req.Len() != 0 {
				request := heap.Pop(&req).(deltaEdge)
				relax(request.dest, request.dist, path.indexOf[request.source.ID()], path, delta, B)
			}

			fmt.Println(B[i].Len())
		}

		req = deltaQueue{}
		for S.Len() != 0 {
			n := heap.Pop(&S).(distanceNode).node
			k := path.indexOf[n.ID()]
			for _, v := range g.From(n) {
				j := path.indexOf[v.ID()]
				if heavy[k][j] {
					w, ok := weight(n, v)
					if !ok {
						panic("delta-step: unexpected invalid weight")
					}
					newCost := w + path.dist[k]
					heap.Push(&req, deltaEdge{dest: v, dist: newCost, source: n})
				}
			}
		}
		for req.Len() != 0 {
			request := heap.Pop(&req).(deltaEdge)
			relax(request.dest, request.dist, path.indexOf[request.source.ID()], path, delta, B)
		}
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

// deltaQueue implements a no-dec priority queue.
type deltaQueue []deltaEdge

func (q deltaQueue) Len() int            { return len(q) }
func (q deltaQueue) Less(i, j int) bool  { return q[i].dist < q[j].dist }
func (q deltaQueue) Swap(i, j int)       { q[i], q[j] = q[j], q[i] }
func (q *deltaQueue) Push(n interface{}) { *q = append(*q, n.(deltaEdge)) }
func (q *deltaQueue) Pop() interface{} {
	t := *q
	var n interface{}
	n, *q = t[len(t)-1], t[:len(t)-1]
	return n
}
