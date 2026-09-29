-- Prove2me | solution 1 for rayleigh_quotient_eq_iff_constant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:58:02.238901+00:00
-- url     : https://prove2.me/submissions/9ea0a846-d9a9-488f-8a28-1faa20d54823

-- Sol generated from MachineLearning/PrimeGaps/Optimization.lean
import Mathlib
import Definitions.Def_MachineLearning_PrimeGaps_Optimization
/-
# Finite-Dimensional Optimization Core of the Maynard Sieve

This file formalizes the exact extremal inequality S₂(w) ≤ k · S₁(w) where
S₁(w) = ∑ wᵢ² and S₂(w) = (∑ wᵢ)², and characterizes equality as holding
iff all weights are equal. This is the finite-dimensional positivity backbone
of the Maynard–Tao bounded gaps argument.

## Main results

* `sum_sq_le_card_mul_sq_sum` — The Cauchy–Schwarz inequality S₂ ≤ k·S₁
* `rayleigh_quotient_bound` — S₂/S₁ ≤ k with division
* `rayleigh_quotient_eq_iff_constant` — Equality iff all weights are equal
* `positiveWeightProfile_exists_iff` — The threshold existence theorem:
    ∃ w with S₂/S₁ > τ ⟺ τ < k
-/


open Finset BigOperators



/-
**Cauchy–Schwarz in finite dimension.** The square of the sum is at most
`k` times the sum of squares. This is the sharp finite-dimensional inequality
underlying Maynard-type weight optimization.
-/

/-
The Rayleigh quotient S₂/S₁ is bounded by k.
-/

/-
**Equality characterization.** S₂ = k·S₁ if and only if all weights are equal.
-/


/-
**Threshold existence theorem.** There exists a weight vector with
S₂/S₁ > τ if and only if τ < k. This is the exact finite-dimensional
optimization threshold for the Maynard sieve.
-/

theorem solution{k : ℕ} (hk : 0 < k) (w : Fin k → ℝ) :
    S2 w = k * S1 w ↔ ∃ c : ℝ, ∀ i, w i = c := by
  constructor <;> intro h;
  · -- By definition of $S2$ and $S1$, we can rewrite the equality as $\sum (w_i - \mu)^2 = 0$, where $\mu = \frac{\sum w_i}{k}$.
    set μ : ℝ := (∑ i, w i) / k
    have h_var : ∑ i, (w i - μ) ^ 2 = 0 := by
      unfold S2 S1 at h;
      simp +decide [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, h, hk.ne' ];
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, h, hk.ne', μ ];
      field_simp;
      linarith;
    exact ⟨ μ, fun i => sub_eq_zero.mp ( by rw [ Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _ ] at h_var; aesop ) ⟩;
  · unfold S2 S1; obtain ⟨ c, hc ⟩ := h; norm_num [ hc ] ; ring;
