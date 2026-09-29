-- Prove2me | Theorems.Thm_positive_level2_shape_is_perm_112
-- name    : positive_level2_shape_is_perm_112
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T09:20:58.613469+00:00
-- url     : https://prove2.me/theorems/4f234260-b2bc-4a15-b05e-1f3cfa3b6af4
-- title:
--   Positive level-two shapes are permutations of 112
-- statement:
--   If three positive natural coordinates sum to four, then the shape is one of the three permutations of (1,1,2).
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

theorem positive_level2_shape_is_perm_112
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 4) :
    IsPerm112 a b c := by sorry
