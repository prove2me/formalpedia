-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_32302080_d9f8_461c_9542_c9cd7d932e42_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_32302080_d9f8_461c_9542_c9cd7d932e42_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:44:14.310638+00:00
-- url     : https://prove2.me/theorems/bc188a74-c743-4521-84db-ff6e1b478f87
-- title:
--   Planar edge upper bound
-- statement:
--   For a graph with the target’s drawing and at least three vertices, its edge count is at most three times the number of vertices minus six. Maximality is retained in the statement for direct compatibility, though the Euler bound itself does not need it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_32302080_d9f8_461c_9542_c9cd7d932e42_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hR : HasPlanarDrawingOn R) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ S : SimpleGraph V, R ≤ S → HasPlanarDrawingOn S → S = R) : ∀ [hRdec : DecidableRel R.Adj], R.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
