-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_exists__p2m_e4b54fa0_8696_482b_974e_2350a87956d8_a1
-- name    : WilliamsonShmoys.maximal_planar_extension_exists__p2m_e4b54fa0_8696_482b_974e_2350a87956d8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:58.568461+00:00
-- url     : https://prove2.me/theorems/693a0634-6764-414a-b500-9400969f72a3
-- title:
--   Existence of an edge-maximal drawable extension
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion among drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_exists__p2m_e4b54fa0_8696_482b_974e_2350a87956d8_a1 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N) : ∃ Q : SimpleGraph V, N.edgeSet ⊆ Q.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧ ∀ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn R → R.edgeSet = Q.edgeSet := by sorry
