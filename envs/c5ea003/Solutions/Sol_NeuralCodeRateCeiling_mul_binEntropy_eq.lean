-- Prove2me | solution 1 for NeuralCodeRateCeiling.mul_binEntropy_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:57:14.001984+00:00
-- url     : https://prove2.me/submissions/1996bf33-2aac-454e-b6f8-f24752dfb292

-- Sol generated from Novelty/NeuralCodeRateCeiling.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds
import Definitions.Def_Novelty_NeuralCodeRateCeiling

/-!
# Neural Coding: the Sphere-Packing Rate Ceiling

`Catalog/Novelty/NeuralCodeCapacityBounds.lean` established the *lower* half of
the rate–distance picture for noise-tolerant neural codes: the Gilbert–Varshamov
theorem says the robust capacity `A(N,d)` of `N` neurons has rate at least
`1 - H₂(δ)` bits per neuron, `δ = (d-1)/N`.  The matching *upper* half needs a
**lower** bound on a binomial coefficient, namely the largest-term estimate

`N ^ N ≤ (N + 1) * r ^ r * (N - r) ^ (N - r) * C(N, r)`,

equivalently `log C(N,r) ≥ N · H(r/N) - log (N+1)`.  That is what this file
proves, and then feeds into the sphere-packing (Hamming) bound to obtain the
**rate ceiling**

`log₂ A(N, 2t+1) / N ≤ 1 - H₂(t/N) + log₂(N+1) / N`.

Together with Gilbert–Varshamov this sandwiches the achievable rate of a
population of `N` neurons that must survive `t` misfirings.

## Main results

* `binTerm_le_center` — the binomial term `C(N,k) r^k (N-r)^(N-k)` is maximal at
  `k = r`: the Bernoulli(`r/N`) distribution on `N` neurons peaks at `r` active
  neurons.  (Proved entirely in `ℕ` by a two-sided ratio argument.)
* `pow_self_le_succ_mul_binTerm` — `N^N ≤ (N+1) * binTerm N r r`, the
  largest-term lower bound for the binomial sum.
* `four_pow_le_central_binom` — the classical corollary `4^n ≤ (2n+1) * C(2n,n)`.
* `log_choose_lower` — `N · H(r/N) - log (N+1) ≤ log C(N,r)`, the entropy lower
  bound on binomial coefficients (the converse of `log_ballVolume_le`).
* `ballVolume_entropy_sandwich` — combining with `log_ballVolume_le`, the volume
  of a Hamming ball of relative radius `δ ≤ 1/2` is `exp (N · H(δ))` up to a
  factor `N + 1`.
* `log_maxCodeSize_le` / `sphere_packing_rate_bits` — the **rate ceiling** for
  `t`-error-correcting neural codes.
* `neural_rate_sandwich` — the two-sided rate estimate: with `δ = t/N`,
  `1 - H₂(2δ) ≤ log₂ A(N,2t+1)/N ≤ 1 - H₂(δ) + log₂(N+1)/N`.
-/

open NeuralCodeRateCeiling

open Finset NeuralCodeCapacity

/-! ## The largest term of a binomial sum -/












/-! ## The entropy lower bound on binomial coefficients -/

private lemma mul_log_div_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a * Real.log (a / b) = a * Real.log a - a * Real.log b := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h]; ring
  · rw [Real.log_div (ne_of_gt h) (ne_of_gt hb)]; ring



/-! ## The rate ceiling for error-correcting neural codes -/









open NeuralCodeRateCeiling in
theorem solution(N r : ℕ) (hN : 0 < N) (hr : r ≤ N) :
    (N : ℝ) * Real.binEntropy ((r : ℝ) / N)
      = N * Real.log N - r * Real.log r - ((N : ℝ) - r) * Real.log ((N : ℝ) - r) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hrN : (r : ℝ) ≤ N := by exact_mod_cast hr
  set p : ℝ := (r : ℝ) / N with hp
  have hNp : (N : ℝ) * p = r := by rw [hp]; field_simp
  have h1p : 1 - p = ((N : ℝ) - r) / N := by rw [hp]; field_simp
  have hN1p : (N : ℝ) * (1 - p) = (N : ℝ) - r := by rw [h1p]; field_simp
  have e1 : (r : ℝ) * Real.log p = r * Real.log r - r * Real.log N := mul_log_div_eq hr0 hN0
  have e2 : ((N : ℝ) - r) * Real.log (1 - p)
      = ((N : ℝ) - r) * Real.log ((N : ℝ) - r) - ((N : ℝ) - r) * Real.log N := by
    rw [h1p]; exact mul_log_div_eq (by linarith) hN0
  rw [Real.binEntropy, Real.log_inv, Real.log_inv]
  have expand : (N : ℝ) * (p * -Real.log p + (1 - p) * -Real.log (1 - p))
      = -(((N : ℝ) * p) * Real.log p) - (((N : ℝ) * (1 - p)) * Real.log (1 - p)) := by ring
  rw [expand, hNp, hN1p, e1, e2]
  ring
