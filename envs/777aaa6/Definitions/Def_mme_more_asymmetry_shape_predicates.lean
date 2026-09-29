-- Prove2me | Definitions.Def_mme_more_asymmetry_shape_predicates
-- name    : mme_more_asymmetry_shape_predicates
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-12T10:05:07.486186+00:00
-- url     : https://prove2.me/theorems/3974632d-a9ff-4bd4-8d45-2aa2db6a7bf7
-- title:
--   Finite 112, 224, and 233 shape predicates
-- statement:
--   This definition packages the three finite coordinate-shape predicates used in the level-three More Asymmetry recursion. IsPerm112 records the three permutations of (1,1,2), while IsPerm224 and IsPerm233 record the permutations of (2,2,4) and (2,3,3). They are shared source-faithful interfaces for the positive level-two and level-three case splits.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions 3.5–3.6 and Theorem 6.4, pp. 14–15 and 28–31.

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


