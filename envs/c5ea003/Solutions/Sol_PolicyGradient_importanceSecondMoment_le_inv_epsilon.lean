-- Prove2me | solution 1 for PolicyGradient.importanceSecondMoment_le_inv_epsilon
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:04:17.21649+00:00
-- url     : https://prove2.me/submissions/846e84f3-2450-46c5-b0ca-0ba3de47af81

-- Sol generated from MachineLearning/PolicyGradient/Theorems.lean
import Mathlib
import Definitions.Def_MachineLearning_PolicyGradient_Theorems
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Finite policy-gradient and exploration-variance theorems

A self-contained finite-action formalization. Policies are differentiable
families of probability vectors. The score identity is represented without
logs by `∂p(a) = p(a) ψ(a)`.
-/

open PolicyGradient

open scoped BigOperators

variable {n d : ℕ}











open PolicyGradient in
theorem solution    (behavior target g : Fin n → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hb : ∀ a, 0 < behavior a)
    (ht : ∀ a, 0 ≤ target a)
    (hexplore : ∀ a, ε * target a ≤ behavior a) :
    importanceSecondMoment behavior target g ≤
      (1 / ε) * expect target (fun a => (g a) ^ 2) := by
  unfold importanceSecondMoment expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hratio : target a / behavior a ≤ 1 / ε := by
    apply (div_le_iff₀ (hb a)).2
    calc
      target a = (1 / ε) * (ε * target a) := by field_simp
      _ ≤ (1 / ε) * behavior a := by
        exact mul_le_mul_of_nonneg_left (hexplore a) (by positivity)
  calc
    behavior a * (target a / behavior a * g a) ^ 2 =
        target a * (target a / behavior a) * (g a) ^ 2 := by
          field_simp
    _ ≤ target a * (1 / ε) * (g a) ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hratio (ht a)) (sq_nonneg _)
    _ = (1 / ε) * (target a * (g a) ^ 2) := by ring
