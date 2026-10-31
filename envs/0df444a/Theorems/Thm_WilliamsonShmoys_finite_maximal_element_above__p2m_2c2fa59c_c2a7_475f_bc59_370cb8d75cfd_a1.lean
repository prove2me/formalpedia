-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_element_above__p2m_2c2fa59c_c2a7_475f_bc59_370cb8d75cfd_a1
-- name    : WilliamsonShmoys.finite_maximal_element_above__p2m_2c2fa59c_c2a7_475f_bc59_370cb8d75cfd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:36:49.149561+00:00
-- url     : https://prove2.me/theorems/b77daa85-8b0a-4a3f-80e0-3fe68f68815c
-- title:
--   Finite posets have maximal elements above a feasible element
-- statement:
--   In a finite partially ordered type, a downward-closed predicate that holds at an element has a maximal satisfying element above it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_element_above__p2m_2c2fa59c_c2a7_475f_bc59_370cb8d75cfd_a1 (α : Type) [Fintype α] [PartialOrder α] (P : α → Prop) (a : α) (ha : P a) (hdown : ∀ ⦃x y : α⦄, x ≤ y → P y → P x) : ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c = b := by sorry
