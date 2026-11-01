-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_exists__p2m_8b952692_ce82_4b1a_b285_daef0e717378_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_8b952692_ce82_4b1a_b285_daef0e717378_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:07:25.961341+00:00
-- url     : https://prove2.me/theorems/3360d2ba-ceaf-4efe-b821-9c16d4398060
-- title:
--   Finite maximal drawable extension
-- statement:
--   Any drawable finite simple graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_8b952692_ce82_4b1a_b285_daef0e717378_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
