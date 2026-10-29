-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_295c0ef8_5d8f_41a3_8c9f_ccd6cdcf9c48_a2
-- name    : WilliamsonShmoys.planar_completion_edge_count__p2m_295c0ef8_5d8f_41a3_8c9f_ccd6cdcf9c48_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T21:32:31.3512+00:00
-- url     : https://prove2.me/theorems/e2c10b97-84b2-4ddf-bc9b-07844206edcc
-- title:
--   Planar graphs have triangulated completions
-- statement:
--   Every graph with a crossing-free drawing on a finite linearly ordered vertex set of size at least three has a drawable supergraph on the same vertices whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_completion_edge_count__p2m_295c0ef8_5d8f_41a3_8c9f_ccd6cdcf9c48_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
