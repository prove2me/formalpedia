-- Prove2me | solution 1 for NeuralCodeRateCeiling.four_pow_le_central_binom
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:57:13.389983+00:00
-- url     : https://prove2.me/submissions/fcf152bb-803e-44c3-9950-0d0beb903f83

-- Sol generated from Novelty/NeuralCodeRateCeiling.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds
import Definitions.Def_Novelty_NeuralCodeRateCeiling
import Theorems.Thm_NeuralCodeRateCeiling_binTerm_step_down
import Theorems.Thm_NeuralCodeRateCeiling_binTerm_step_up

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






private lemma binTerm_le_center_of_le {N r : ℕ} (hr : r ≤ N) :
    ∀ j k : ℕ, k + j = r → binTerm N r k ≤ binTerm N r r := by
  intro j
  induction j with
  | zero => intro k hk; simp only [Nat.add_zero] at hk; subst hk; exact le_rfl
  | succ j ih => intro k hk; exact le_trans (binTerm_step_up hr (by omega)) (ih (k + 1) (by omega))

private lemma binTerm_le_center_of_ge {N r : ℕ} (hr : r ≤ N) :
    ∀ j k : ℕ, k = r + j → k ≤ N → binTerm N r k ≤ binTerm N r r := by
  intro j
  induction j with
  | zero => intro k hk _; simp only [Nat.add_zero] at hk; subst hk; exact le_rfl
  | succ j ih =>
      intro k hk hkN
      have h1 : k = (r + j) + 1 := by omega
      subst h1
      exact le_trans (binTerm_step_down hr (by omega) (by omega)) (ih (r + j) rfl (by omega))

/-- **The binomial distribution with parameter `r/N` peaks at `r`.**  Among all
activity levels `k`, the weight `C(N,k) r^k (N-r)^(N-k)` is largest at `k = r`. -/
theorem binTerm_le_center {N r k : ℕ} (hr : r ≤ N) (hk : k ≤ N) :
    binTerm N r k ≤ binTerm N r r := by
  rcases le_total k r with h | h
  · exact binTerm_le_center_of_le hr (r - k) k (by omega)
  · exact binTerm_le_center_of_ge hr (k - r) k (by omega) hk

/-- The binomial expansion of `N ^ N` in terms of `r` and `N - r`. -/
lemma sum_binTerm {N r : ℕ} (hr : r ≤ N) :
    ∑ k ∈ Finset.range (N + 1), binTerm N r k = N ^ N := by
  have h := add_pow (r : ℕ) (N - r) N
  rw [Nat.add_sub_cancel' hr] at h
  rw [h]
  exact Finset.sum_congr rfl (fun k _ => by simp [binTerm])

/-- **Largest-term bound.**  The single largest term of the binomial expansion of
`N ^ N` already accounts for at least a `1/(N+1)` fraction of it. -/
theorem pow_self_le_succ_mul_binTerm {N r : ℕ} (hr : r ≤ N) :
    N ^ N ≤ (N + 1) * binTerm N r r := by
  calc N ^ N = ∑ k ∈ Finset.range (N + 1), binTerm N r k := (sum_binTerm hr).symm
    _ ≤ ∑ _k ∈ Finset.range (N + 1), binTerm N r r :=
        Finset.sum_le_sum fun k hk =>
          binTerm_le_center hr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    _ = (N + 1) * binTerm N r r := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]


/-! ## The entropy lower bound on binomial coefficients -/




/-! ## The rate ceiling for error-correcting neural codes -/









open NeuralCodeRateCeiling in
theorem solution(n : ℕ) : 4 ^ n ≤ (2 * n + 1) * (2 * n).choose n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := pow_self_le_succ_mul_binTerm (N := 2 * n) (r := n) (by omega)
  have hsub : 2 * n - n = n := by omega
  have hb : binTerm (2 * n) n n = n ^ (2 * n) * (2 * n).choose n := by
    unfold binTerm
    rw [hsub, ← pow_add]
    ring_nf
  have hlhs : (2 * n) ^ (2 * n) = 4 ^ n * n ^ (2 * n) := by
    rw [mul_pow]
    congr 1
    rw [pow_mul]
    norm_num
  rw [hb, hlhs] at h
  have hpos : 0 < n ^ (2 * n) := Nat.pow_pos hn
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc 4 ^ n * n ^ (2 * n) ≤ (2 * n + 1) * (n ^ (2 * n) * (2 * n).choose n) := h
    _ = (2 * n + 1) * (2 * n).choose n * n ^ (2 * n) := by ring
