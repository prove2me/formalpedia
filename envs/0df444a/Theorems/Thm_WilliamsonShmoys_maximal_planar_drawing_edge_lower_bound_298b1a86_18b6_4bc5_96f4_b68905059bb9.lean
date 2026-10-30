-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_298b1a86_18b6_4bc5_96f4_b68905059bb9
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_298b1a86_18b6_4bc5_96f4_b68905059bb9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:20:59.114695+00:00
-- url     : https://prove2.me/theorems/2ceaf4d0-5af9-47dd-acbb-6f6d51630a18
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   An inclusion-maximal graph with this crossing-free drawing predicate and at least three vertices has at least 3|V|−6 edges. The proof uses maximality to force a triangulated embedding (with the three-vertex boundary case handled by forcing all three edges), then Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_298b1a86_18b6_4bc5_96f4_b68905059bb9
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by
  sorry
