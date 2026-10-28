-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:43:25.630306+00:00
-- url     : https://prove2.me/theorems/c36a113f-0775-4b60-9c1c-cf7701a1310e
-- title:
--   Edge maximality forces the planar lower bound
-- statement:
--   If a graph on at least three vertices admits the specified crossing-free drawing and no planar supergraph on the same vertices has more edges, then it has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  sorry
