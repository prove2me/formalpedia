-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_3e222915_cdcc_42d9_bbed_07142c562af3_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_3e222915_cdcc_42d9_bbed_07142c562af3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:53:34.78172+00:00
-- url     : https://prove2.me/theorems/f8388283-f9ed-4c0f-b0f7-c6403411f5ff
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three fixed vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_3e222915_cdcc_42d9_bbed_07142c562af3_a1 {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X) (hV : 3 ≤ Fintype.card V) (hmax : ∀ Y : SimpleGraph V, X ≤ Y → WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X) : X.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
