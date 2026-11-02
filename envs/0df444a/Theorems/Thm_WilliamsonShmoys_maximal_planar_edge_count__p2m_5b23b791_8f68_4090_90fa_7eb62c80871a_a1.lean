-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5b23b791_8f68_4090_90fa_7eb62c80871a_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_5b23b791_8f68_4090_90fa_7eb62c80871a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:36:44.721811+00:00
-- url     : https://prove2.me/theorems/32302080-d9f8-461c-9542-c9cd7d932e42
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite linearly ordered vertex type with at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_5b23b791_8f68_4090_90fa_7eb62c80871a_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hR : HasPlanarDrawingOn R) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ S : SimpleGraph V, R ≤ S → HasPlanarDrawingOn S → S = R) : ∀ [hRdec : DecidableRel R.Adj], R.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
