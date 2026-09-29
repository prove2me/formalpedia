-- Prove2me | Theorems.Thm_mme_finite_word_family_histogram_entropy_upper
-- name    : mme_finite_word_family_histogram_entropy_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T03:51:29.954171+00:00
-- url     : https://prove2.me/theorems/2e23243e-4447-4740-b405-761ff7bb8a38
-- title:
--   Finite word-family bound from empirical histogram entropy
-- statement:
--   A finite family of length-n words over R has at most (n+1)^|R| empirical histograms. If every family member has empirical entropy at most H, then the family cardinal is at most (n+1)^|R| exp(n log(2) H).
-- source:
--   R. Duan, H. Wu, and R. Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Algorithm 2 and Section 3.10; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_multinomial_entropy_upper
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open scoped BigOperators

set_option autoImplicit false

theorem mme_finite_word_family_histogram_entropy_upper
    {R : Type*} [Fintype R] [DecidableEq R]
    (n : ℕ) (hn : 0 < n)
    (F : Finset (Fin n → R)) (H : ℝ)
    (hH : ∀ f ∈ F,
      mme_modern_entropyBits
          (fun r ↦ (Fintype.card {t : Fin n // f t = r} : ℝ) / (n : ℝ)) ≤ H) :
    (F.card : ℝ) ≤
      (((n + 1 : ℕ) : ℝ)) ^ Fintype.card R *
        Real.exp ((n : ℝ) * Real.log 2 * H) := by
  sorry
