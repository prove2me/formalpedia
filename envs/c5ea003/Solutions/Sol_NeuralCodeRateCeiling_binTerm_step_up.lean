-- Prove2me | solution 1 for NeuralCodeRateCeiling.binTerm_step_up
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:55:38.149314+00:00
-- url     : https://prove2.me/submissions/ef7f3d57-0192-4fe6-b6e9-fc994d5baf5c

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


/-- Ratio inequality driving the increasing half: for `k + 1 ≤ r`. -/
private lemma key_up {N r k : ℕ} (hr : r ≤ N) (hk : k + 1 ≤ r) :
    (k + 1) * (N - r) ≤ (N - k) * r := by
  have h1 : k ≤ N := by omega
  have hk' : ((k : ℤ) + 1) ≤ (r : ℤ) := by exact_mod_cast hk
  have hr' : (r : ℤ) ≤ (N : ℤ) := by exact_mod_cast hr
  have hN0 : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
  have hr0 : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
  zify [hr, h1]
  nlinarith










/-! ## The entropy lower bound on binomial coefficients -/




/-! ## The rate ceiling for error-correcting neural codes -/









open NeuralCodeRateCeiling in
theorem solution{N r k : ℕ} (hr : r ≤ N) (hk : k + 1 ≤ r) :
    binTerm N r k ≤ binTerm N r (k + 1) := by
  have hchoose : N.choose (k + 1) * (k + 1) = N.choose k * (N - k) :=
    Nat.choose_succ_right_eq N k
  have hb : (N - r) ^ (N - k) = (N - r) ^ (N - (k + 1)) * (N - r) := by
    have h : N - k = (N - (k + 1)) + 1 := by omega
    rw [h, pow_succ]
  have e1 : (k + 1) * binTerm N r k
      = (r ^ k * (N - r) ^ (N - (k + 1)) * N.choose k) * ((k + 1) * (N - r)) := by
    unfold binTerm; rw [hb]; ring
  have e2 : (k + 1) * binTerm N r (k + 1)
      = (r ^ k * (N - r) ^ (N - (k + 1)) * N.choose k) * ((N - k) * r) := by
    unfold binTerm
    calc (k + 1) * (r ^ (k + 1) * (N - r) ^ (N - (k + 1)) * N.choose (k + 1))
        = (r ^ k * (N - r) ^ (N - (k + 1))) * (N.choose (k + 1) * (k + 1)) * r := by ring
      _ = (r ^ k * (N - r) ^ (N - (k + 1))) * (N.choose k * (N - k)) * r := by rw [hchoose]
      _ = _ := by ring
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos k)
  rw [e1, e2]
  exact Nat.mul_le_mul_left _ (key_up hr hk)
