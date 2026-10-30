-- Prove2me | Theorems.Thm_finite_finset_maximal_element__p2m_e3d00913_05dd_434d_bc2d_b9a3208fb1a4_a1
-- name    : finite_finset_maximal_element__p2m_e3d00913_05dd_434d_bc2d_b9a3208fb1a4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:21:13.22118+00:00
-- url     : https://prove2.me/theorems/7893aa0a-120a-424a-af92-4f6619774471
-- title:
--   A feasible finset has an inclusion-maximal feasible extension
-- statement:
--   For a finite type α, any nonempty family of finsets satisfying P has an inclusion-maximal member. The statement is nonempty through the supplied witness s₀ and does not assume P is monotone.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_finset_maximal_element__p2m_e3d00913_05dd_434d_bc2d_b9a3208fb1a4_a1 {α : Type} [Fintype α] (P : Finset α → Prop) (s₀ : Finset α) (hs₀ : P s₀) : ∃ s, P s ∧ ∀ t, s ⊂ t → ¬ P t := by sorry
