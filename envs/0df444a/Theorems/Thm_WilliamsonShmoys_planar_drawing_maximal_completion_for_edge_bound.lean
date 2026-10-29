-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_completion_for_edge_bound
-- name    : WilliamsonShmoys.planar_drawing_maximal_completion_for_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:06:37.807416+00:00
-- url     : https://prove2.me/theorems/e9c82dc3-e247-48ae-989d-76bf4073323a
-- title:
--   Maximal planar completion for an edge bound
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges, and the original graph has no more edges than that supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_completion_for_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard := by sorry
