-- Prove2me | Theorems.Thm_mme_more_asymmetry_positive_level2_shape_explicit
-- name    : mme_more_asymmetry_positive_level2_shape_explicit
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T10:12:56.202803+00:00
-- url     : https://prove2.me/theorems/614de4d4-3233-40cc-8a1d-ad457190f1c0
-- title:
--   Positive level-two shapes are explicit permutations of 112
-- statement:
--   If three positive natural coordinates sum to four, then the shape is one of the three permutations of (1,1,2), stated without a local preamble definition so the worker can package the theorem directly.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions 3.5–3.6 and Theorem 6.4, pp. 14–15 and 28–31.

import Mathlib.Tactic

set_option autoImplicit false

theorem mme_more_asymmetry_positive_level2_shape_explicit
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 4) :
    (a = 1 ∧ b = 1 ∧ c = 2) ∨
      (a = 1 ∧ b = 2 ∧ c = 1) ∨
      (a = 2 ∧ b = 1 ∧ c = 1) := by sorry
