-- Prove2me | solution 1 for mme_CW_square_support_sum_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-23T23:06:08.390207+00:00
-- url     : https://prove2.me/submissions/264fa787-db32-4c86-b370-02cf1bb49b52

import Theorems.Thm_mme_CW_block_kronPow_MM_corrected

open MME

/-!
The six CW support triples all have natural coordinate sum two.  Adding the
grades of two supported monomials, as in the regrouping of `T_q ⊗ T_q`,
therefore gives the five-class invariant `I + J + K = 4` from CW90 (11).
-/

theorem solution
    (s₁ s₂ : Fin 3 × Fin 3 × Fin 3)
    (h₁ : s₁ ∈ CWSupportPattern)
    (h₂ : s₂ ∈ CWSupportPattern) :
    (s₁.1.val + s₂.1.val) +
      (s₁.2.1.val + s₂.2.1.val) +
      (s₁.2.2.val + s₂.2.2.val) = 4 := by
  unfold CWSupportPattern at h₁ h₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
  rcases h₁ with h₁ | h₁ | h₁ | h₁ | h₁ | h₁ <;>
    rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ <;>
    subst s₁ <;> subst s₂ <;> decide
