-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:05:02.79563+00:00
-- url     : https://prove2.me/theorems/42a32245-904d-4102-8e18-0dd359dce9a3
-- title:
--   Maximal planar edge-count lower bound
-- statement:
--   A drawable graph on at least three vertices that admits no strictly larger drawable graph on the same vertex set has at least 3n−6 edges. This isolates the saturation and triangulation argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : HasPlanarDrawingOn L) (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) : 3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
