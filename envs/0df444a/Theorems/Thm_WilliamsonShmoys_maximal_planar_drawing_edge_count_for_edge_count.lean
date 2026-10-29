-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_edge_count
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:39:37.729762+00:00
-- url     : https://prove2.me/theorems/4095a92f-6e84-438b-9034-42ed5248706c
-- title:
--   Edge count of a maximal drawable graph for completion
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertices has exactly 3|V|−6 edges. Convert its crossing-free drawing into a plane embedding, use maximality to rule out disconnected components and nontriangular faces, then apply Euler’s formula and the fact that face degrees sum to twice the number of edges. At |V| = 3 this gives the triangle. This isolates the topological and counting work from the finite maximality argument in the other child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
