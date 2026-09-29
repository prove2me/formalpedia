-- Prove2me | Theorems.Thm_positive_level3_two_interior_children_iff_perm_224_or_233
-- name    : positive_level3_two_interior_children_iff_perm_224_or_233
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T09:20:57.853796+00:00
-- url     : https://prove2.me/theorems/d445d05e-dda0-416f-bcf9-15712050d4ec
-- title:
--   Two positive 112 children occur only in shapes 224 or 233
-- statement:
--   A level-three shape is the coordinatewise sum of two positive level-two 112 shapes exactly when it is a permutation of 224 or 233.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions 3.5-3.6 and Theorem 6.4, pp. 14-15 and 28-31; exact q=5 level-3 coarse support. This finite combinatorial helper records that every positive level-2 shape summing to four is a permutation of 112, and that two such children sum only to a permutation of 224 or 233.

import Mathlib.Tactic

set_option autoImplicit false

def IsPerm112 (a b c : ℕ) : Prop :=
  (a = 1 ∧ b = 1 ∧ c = 2) ∨
  (a = 1 ∧ b = 2 ∧ c = 1) ∨
  (a = 2 ∧ b = 1 ∧ c = 1)

def IsPerm224 (a b c : ℕ) : Prop :=
  (a = 2 ∧ b = 2 ∧ c = 4) ∨
  (a = 2 ∧ b = 4 ∧ c = 2) ∨
  (a = 4 ∧ b = 2 ∧ c = 2)

def IsPerm233 (a b c : ℕ) : Prop :=
  (a = 2 ∧ b = 3 ∧ c = 3) ∨
  (a = 3 ∧ b = 2 ∧ c = 3) ∨
  (a = 3 ∧ b = 3 ∧ c = 2)

theorem positive_level3_two_interior_children_iff_perm_224_or_233
    (i j k : ℕ) :
    (∃ a₁ b₁ c₁ a₂ b₂ c₂ : ℕ,
      IsPerm112 a₁ b₁ c₁ ∧ IsPerm112 a₂ b₂ c₂ ∧
      a₁ + a₂ = i ∧ b₁ + b₂ = j ∧ c₁ + c₂ = k) ↔
      IsPerm224 i j k ∨ IsPerm233 i j k := by sorry
