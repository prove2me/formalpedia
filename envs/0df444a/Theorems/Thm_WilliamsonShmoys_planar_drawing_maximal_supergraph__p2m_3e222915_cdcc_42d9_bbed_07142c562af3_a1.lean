-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_3e222915_cdcc_42d9_bbed_07142c562af3_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_3e222915_cdcc_42d9_bbed_07142c562af3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:53:32.895782+00:00
-- url     : https://prove2.me/theorems/bf001e0e-24f9-43c1-8004-bdc368085703
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph on a fixed finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under graph inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_3e222915_cdcc_42d9_bbed_07142c562af3_a1 {V : Type} [Fintype V] [LinearOrder V] (W : SimpleGraph V) (hW : WilliamsonShmoys.HasPlanarDrawingOn W) : ∃ X : SimpleGraph V, W ≤ X ∧ WilliamsonShmoys.HasPlanarDrawingOn X ∧ ∀ Y : SimpleGraph V, X ≤ Y → WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X := by sorry
