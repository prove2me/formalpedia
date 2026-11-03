-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_9987107f_9ded_4251_bab3_dd81d8d6e153_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_9987107f_9ded_4251_bab3_dd81d8d6e153_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:53:55.500823+00:00
-- url     : https://prove2.me/theorems/263e0430-0bed-4695-a55f-33a5be744a5b
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Every finite simple graph with a drawing satisfying HasPlanarDrawingOn and at least three vertices has at most 3|V| − 6 edges. The component cases of sizes one and two must be included when applying the connected planar bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_9987107f_9ded_4251_bab3_dd81d8d6e153_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     N.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  sorry
