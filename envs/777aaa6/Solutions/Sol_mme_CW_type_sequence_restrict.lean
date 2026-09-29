-- Prove2me | solution 1 for mme_CW_type_sequence_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-23T22:50:06.352204+00:00
-- url     : https://prove2.me/submissions/1088570c-09c6-4c7e-aa59-4b9f5f640acc

import Theorems.Thm_mme_CW_block_kronPow_MM_corrected
import Theorems.Thm_mme_CW_block_dimension_products

open MME BigOperators

universe u

/-!
For a type sequence in the six-element CW support, each mode dimension is a
power of `q`.  The exponent is the number of occurrences of the unique
middle-type carrying `q` in that mode.  This is the exact block bookkeeping
behind CW90, Section 7, pp. 262--263.
-/

theorem solution {K : Type u} [Field K] (q N : ℕ)
    (τ : Fin N → Fin 3 × Fin 3 × Fin 3)
    (hτ : ∀ k : Fin N, τ k ∈ CWSupportPattern) :
    TensorObj.Restrict
      (MMObj K
        (q ^ (Finset.univ.filter (fun k : Fin N => τ k = (1, 0, 1))).card)
        (q ^ (Finset.univ.filter (fun k : Fin N => τ k = (1, 1, 0))).card)
        (q ^ (Finset.univ.filter (fun k : Fin N => τ k = (0, 1, 1))).card))
      ((CWObj K q).kronPow N) := by
  have h := mme_CW_block_kronPow_MM_corrected (K := K) q N τ hτ
  rcases mme_CW_block_dimension_products q N τ with ⟨hx, hy, hz⟩
  rw [hx, hy, hz] at h
  exact h
