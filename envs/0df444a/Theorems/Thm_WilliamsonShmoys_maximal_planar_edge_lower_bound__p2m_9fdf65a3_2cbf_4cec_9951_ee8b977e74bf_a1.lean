-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:37:08.047077+00:00
-- url     : https://prove2.me/theorems/e995c31f-f3b5-4725-a317-b6f1bf350c0c
-- title:
--   Lower bound for maximal drawable graphs
-- statement:
--   A drawable graph on at least three vertices that has no drawable supergraph on the same vertex set has at least 3|V|−6 edges. This captures the augmentation/triangulation direction needed for the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) (hMax : ∀ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) : 3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
