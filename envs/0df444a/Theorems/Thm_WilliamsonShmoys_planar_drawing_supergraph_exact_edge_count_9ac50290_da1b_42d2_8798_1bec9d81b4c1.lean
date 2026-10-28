-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_exact_edge_count_9ac50290_da1b_42d2_8798_1bec9d81b4c1
-- name    : WilliamsonShmoys.planar_drawing_supergraph_exact_edge_count_9ac50290_da1b_42d2_8798_1bec9d81b4c1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:39:32.343665+00:00
-- url     : https://prove2.me/theorems/24bcd821-2a94-4cb2-b06f-eb5106ed464b
-- title:
--   Planar supergraph with exact edge count
-- statement:
--   Every finite simple graph with a planar drawing and at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges. The vertex lower bound covers the boundary case |V| = 3. The child removes the geometric completion and Euler-counting work from the parent; an independent route is to add noncrossing edges until all faces are triangular, then count edge-face incidences using Euler’s formula. This is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_supergraph_exact_edge_count_9ac50290_da1b_42d2_8798_1bec9d81b4c1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
