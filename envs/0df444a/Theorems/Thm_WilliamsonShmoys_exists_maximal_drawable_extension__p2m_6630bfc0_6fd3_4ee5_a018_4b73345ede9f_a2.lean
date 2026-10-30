-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_extension__p2m_6630bfc0_6fd3_4ee5_a018_4b73345ede9f_a2
-- name    : WilliamsonShmoys.exists_maximal_drawable_extension__p2m_6630bfc0_6fd3_4ee5_a018_4b73345ede9f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:43:21.808235+00:00
-- url     : https://prove2.me/theorems/d84d5cee-c0b6-4b88-aeb6-1ecc3a40a67b
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on that same vertex type with no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_extension__p2m_6630bfc0_6fd3_4ee5_a018_4b73345ede9f_a2 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (hDraw : HasPlanarDrawingOn P) : ∃ Q : SimpleGraph V, P ≤ Q ∧ HasPlanarDrawingOn Q ∧ ∀ R : SimpleGraph V, Q ≤ R → HasPlanarDrawingOn R → R ≤ Q := by sorry
