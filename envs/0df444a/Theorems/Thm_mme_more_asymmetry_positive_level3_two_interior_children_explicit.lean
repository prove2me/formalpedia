-- Prove2me | Theorems.Thm_mme_more_asymmetry_positive_level3_two_interior_children_explicit
-- name    : mme_more_asymmetry_positive_level3_two_interior_children_explicit
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T10:13:01.549983+00:00
-- url     : https://prove2.me/theorems/f5f11d4f-3e42-4dc2-a6ac-131c8c346a63
-- title:
--   Two positive 112 children occur only in explicit 224 or 233 shapes
-- statement:
--   A level-three shape is the coordinatewise sum of two positive level-two 112 shapes exactly when it is an explicit permutation of (2,2,4) or (2,3,3), with no local preamble definition.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions 3.5–3.6 and Theorem 6.4, pp. 14–15 and 28–31.

import Mathlib.Tactic

set_option autoImplicit false

theorem mme_more_asymmetry_positive_level3_two_interior_children_explicit
    (i j k : ℕ) :
    (∃ a₁ b₁ c₁ a₂ b₂ c₂ : ℕ,
      ((a₁ = 1 ∧ b₁ = 1 ∧ c₁ = 2) ∨
        (a₁ = 1 ∧ b₁ = 2 ∧ c₁ = 1) ∨
        (a₁ = 2 ∧ b₁ = 1 ∧ c₁ = 1)) ∧
      ((a₂ = 1 ∧ b₂ = 1 ∧ c₂ = 2) ∨
        (a₂ = 1 ∧ b₂ = 2 ∧ c₂ = 1) ∨
        (a₂ = 2 ∧ b₂ = 1 ∧ c₂ = 1)) ∧
      a₁ + a₂ = i ∧ b₁ + b₂ = j ∧ c₁ + c₂ = k) ↔
      (((i = 2 ∧ j = 2 ∧ k = 4) ∨
        (i = 2 ∧ j = 4 ∧ k = 2) ∨
        (i = 4 ∧ j = 2 ∧ k = 2)) ∨
       ((i = 2 ∧ j = 3 ∧ k = 3) ∨
        (i = 3 ∧ j = 2 ∧ k = 3) ∨
        (i = 3 ∧ j = 3 ∧ k = 2))) := by sorry
