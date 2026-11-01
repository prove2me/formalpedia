-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_f84a2b8d_758d_48e3_856e_f835c2dfd776_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_f84a2b8d_758d_48e3_856e_f835c2dfd776_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:16:37.370052+00:00
-- url     : https://prove2.me/theorems/bef9e736-66c4-4a44-9d5c-f3c0ae5dba68
-- title:
--   Planar edge-count upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most three times its vertex count minus six edges. This supplies the upper inequality. A proof route uses Euler’s formula and face-boundary counting, with a separate reduction or count for disconnected graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_f84a2b8d_758d_48e3_856e_f835c2dfd776_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
      N.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
