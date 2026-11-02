-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_aa8c3543_6a70_4578_ab0d_df04a85e5168_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_aa8c3543_6a70_4578_ab0d_df04a85e5168_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:23:55.516214+00:00
-- url     : https://prove2.me/theorems/7d2c473c-b633-40d1-8c8b-d27ca4a0e11f
-- title:
--   Same-vertex planar triangulation extension
-- statement:
--   Every finite simple graph on at least three linearly ordered vertices that has a drawing satisfying `HasPlanarDrawingOn` extends, on the same vertex set, to a graph with such a drawing and exactly `3 * |V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_aa8c3543_6a70_4578_ab0d_df04a85e5168_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hR : HasPlanarDrawingOn R) (hcard : 3 ≤ Fintype.card V) : ∃ S : SimpleGraph V, R ≤ S ∧ HasPlanarDrawingOn S ∧ ∀ [hSdec : DecidableRel S.Adj], S.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
