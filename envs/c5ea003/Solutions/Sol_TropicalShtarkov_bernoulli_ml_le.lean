-- Prove2me | solution 1 for TropicalShtarkov.bernoulli_ml_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:56:40.316982+00:00
-- url     : https://prove2.me/submissions/3a0f45c0-6698-41f2-b7b7-02f88bae6c27

-- Sol generated from Tropical/Shtarkov/Basic.lean
import Mathlib
import Definitions.Def_Tropical_Shtarkov_Basic
/-
# Tropical Shtarkov Sums: the abstract layer

## Bridge: max-plus (tropical) algebra ↔ universal source coding ↔ counting

The *Shtarkov sum* (a.k.a. the normalizing constant of the normalized maximum
likelihood distribution) of a model class `{P i}` on a finite sample space `X` is

  `S(P) = ∑_{x ∈ X} sup_i P i x`.

The inner `sup` is exactly a **tropical (max-plus) sum** of the log-likelihoods:
`log sup_i P i x = ⊕_i log P i x`, so `S(P)` is the classical mass of the
tropicalisation of the class, and `log S(P)` is the minimax pointwise regret of
the class.  This file develops the two structural tools used throughout:

* `shtarkovSum_ge_packing` — a *packing* lower bound: any collection of
  (sample, model) pairs contributes to `S`;
* `shtarkovSum_le_card_image` — a *sufficient statistic* upper bound: if the
  pointwise supremum is dominated by a sub-probability measure depending on `x`
  only through a statistic `T`, then `S ≤ |image T|`.

Together with the one-dimensional maximum-likelihood inequality
`bernoulli_ml_le` these give matching upper/lower bounds for finite-state
classes in `Catalog/Tropical/Shtarkov/FiniteState.lean`.
-/


open Finset

open TropicalShtarkov

/-! ## The Shtarkov sum -/

variable {X ι : Type*} [Fintype X]







/-! ## The one-dimensional maximum-likelihood inequality

For a Bernoulli source observed `a` times as `true` and `b` times as `false`,
the likelihood `θ^a (1-θ)^b` is maximised at the empirical frequency
`a / (a+b)`.  This is the analytic core of the finite-state upper bound; the
proof is the Gibbs/`log x ≤ x - 1` argument. -/







open TropicalShtarkov in
theorem solution(a b : ℕ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ ^ a * (1 - θ) ^ b ≤ mlParam a b ^ a * (1 - mlParam a b) ^ b := by
  have hθ1 : (0:ℝ) ≤ 1 - θ := by linarith
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hm : mlParam 0 b = 0 := by unfold mlParam; split <;> simp
    rw [hm]
    simp only [pow_zero, one_mul, sub_zero, one_pow, mul_one]
    exact pow_le_one₀ hθ1 (by linarith)
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    have hm : mlParam a 0 = 1 := by
      unfold mlParam
      rw [if_neg (by omega)]
      have h : (0:ℝ) < a := by exact_mod_cast ha
      rw [Nat.cast_zero, add_zero, div_self (ne_of_gt h)]
    rw [hm]
    simp only [pow_zero, mul_one, one_pow, sub_self]
    exact pow_le_one₀ h0 h1
  have hab : ¬ a + b = 0 := by omega
  set t := mlParam a b with ht
  have hA : (0:ℝ) < a := by exact_mod_cast ha
  have hB : (0:ℝ) < b := by exact_mod_cast hb
  have hsum : (0:ℝ) < (a:ℝ) + b := by linarith
  have htv : t = (a:ℝ) / ((a:ℝ) + b) := by rw [ht]; unfold mlParam; rw [if_neg hab]
  have ht0 : 0 < t := by rw [htv]; positivity
  have ht1 : t < 1 := by rw [htv, div_lt_one hsum]; linarith
  have h1t : 1 - t = (b:ℝ) / ((a:ℝ) + b) := by rw [htv]; field_simp; ring
  have hRHS : 0 < t ^ a * (1 - t) ^ b := mul_pos (pow_pos ht0 a) (pow_pos (by linarith) b)
  rcases eq_or_lt_of_le h0 with h | hθ0
  · have hz : θ ^ a = 0 := by rw [← h]; exact zero_pow (by omega)
    rw [hz, zero_mul]; exact hRHS.le
  rcases eq_or_lt_of_le h1 with h | hθlt
  · have hz : (1 - θ) ^ b = 0 := by
      rw [h, sub_self]; exact zero_pow (by omega)
    rw [hz, mul_zero]; exact hRHS.le
  have hLHS : 0 < θ ^ a * (1 - θ) ^ b :=
    mul_pos (pow_pos hθ0 a) (pow_pos (by linarith) b)
  rw [← Real.log_le_log_iff hLHS hRHS,
    Real.log_mul (ne_of_gt (pow_pos hθ0 a)) (ne_of_gt (pow_pos (by linarith) b)),
    Real.log_mul (ne_of_gt (pow_pos ht0 a)) (ne_of_gt (pow_pos (by linarith : (0:ℝ) < 1 - t) b)),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  have k1 : Real.log θ - Real.log t ≤ θ / t - 1 := by
    rw [← Real.log_div (ne_of_gt hθ0) (ne_of_gt ht0)]
    exact Real.log_le_sub_one_of_pos (div_pos hθ0 ht0)
  have k2 : Real.log (1 - θ) - Real.log (1 - t) ≤ (1 - θ) / (1 - t) - 1 := by
    rw [← Real.log_div (by linarith) (by linarith)]
    exact Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
  have hzero : (a:ℝ) * (θ / t - 1) + (b:ℝ) * ((1 - θ) / (1 - t) - 1) = 0 := by
    have d1 : θ / t = θ * ((a:ℝ) + b) / a := by rw [htv]; field_simp
    have d2 : (1 - θ) / (1 - t) = (1 - θ) * ((a:ℝ) + b) / b := by rw [h1t]; field_simp
    rw [d1, d2]
    field_simp
    ring
  have step1 := mul_le_mul_of_nonneg_left k1 hA.le
  have step2 := mul_le_mul_of_nonneg_left k2 hB.le
  nlinarith [step1, step2, hzero]
