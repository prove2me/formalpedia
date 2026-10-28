-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_from_arc_drawing
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_from_arc_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T18:21:16.422142+00:00
-- url     : https://prove2.me/theorems/faaef0db-f949-4633-b30b-82bc3430d246
-- title:
--   Edge count of a maximal graph with an arc drawing
-- statement:
--   Every inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. The proof must connect the supplied crossing-free arc drawing to the planar embedding argument: maximality forces triangular faces, and Euler’s formula together with the sum of face degrees gives the edge count. The case |V|=3 yields the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_from_arc_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
