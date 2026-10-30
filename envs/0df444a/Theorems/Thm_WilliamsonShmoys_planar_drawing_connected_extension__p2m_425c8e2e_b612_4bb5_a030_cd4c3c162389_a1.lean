-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_425c8e2e_b612_4bb5_a030_cd4c3c162389_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_425c8e2e_b612_4bb5_a030_cd4c3c162389_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T00:31:59.362185+00:00
-- url     : https://prove2.me/theorems/5f60d79e-7bc9-419f-998e-e61c453c0681
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   Every finite drawable simple graph has a connected drawable supergraph on the same vertex type that retains every original edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_425c8e2e_b612_4bb5_a030_cd4c3c162389_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
