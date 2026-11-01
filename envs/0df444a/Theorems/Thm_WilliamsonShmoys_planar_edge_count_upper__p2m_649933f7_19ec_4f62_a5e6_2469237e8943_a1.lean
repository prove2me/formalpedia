-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_649933f7_19ec_4f62_a5e6_2469237e8943_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper__p2m_649933f7_19ec_4f62_a5e6_2469237e8943_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:33:59.52544+00:00
-- url     : https://prove2.me/theorems/a49ca777-83c4-4524-a92f-84ff8c99b9bc
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   For a finite simple graph with a planar drawing and at least three vertices, twice its edge count plus twelve is at most six times its vertex count. The three-vertex boundary is included; the hypotheses exclude the smaller cases where this form of the inequality fails.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper__p2m_649933f7_19ec_4f62_a5e6_2469237e8943_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    : letI : DecidableRel M.Adj := dM
      2 * M.edgeFinset.card + 12 ≤ 6 * Fintype.card V := by sorry
