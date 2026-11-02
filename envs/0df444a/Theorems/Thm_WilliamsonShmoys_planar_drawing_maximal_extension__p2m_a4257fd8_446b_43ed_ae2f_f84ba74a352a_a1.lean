-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_a4257fd8_446b_43ed_ae2f_f84ba74a352a_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a4257fd8_446b_43ed_ae2f_f84ba74a352a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:11:29.58761+00:00
-- url     : https://prove2.me/theorems/813de8ea-e58e-48bb-807f-43145eda7132
-- title:
--   Existence of an edge maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a4257fd8_446b_43ed_ae2f_f84ba74a352a_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) := by sorry
