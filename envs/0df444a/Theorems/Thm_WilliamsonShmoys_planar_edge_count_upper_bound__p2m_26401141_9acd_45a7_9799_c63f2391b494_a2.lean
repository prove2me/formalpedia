-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_26401141_9acd_45a7_9799_c63f2391b494_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_26401141_9acd_45a7_9799_c63f2391b494_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:56:26.275248+00:00
-- url     : https://prove2.me/theorems/689905d5-9339-49d2-b742-282bafad4717
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A simple graph with a crossing-free drawing on at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_26401141_9acd_45a7_9799_c63f2391b494_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ H : SimpleGraph V, DecidableRel H.Adj :=
      fun H => Classical.decRel H.Adj
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  sorry
