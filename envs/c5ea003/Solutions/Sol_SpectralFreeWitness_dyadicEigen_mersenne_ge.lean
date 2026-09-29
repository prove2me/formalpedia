-- Prove2me | solution 1 for SpectralFreeWitness.dyadicEigen_mersenne_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:43:16.68623+00:00
-- url     : https://prove2.me/submissions/f1618ed6-49f2-4e37-a58d-195e45464b7e

-- Sol generated from Speculative/AutoResearch/SpectralFreeWitnessSharp.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
/-
# Sharpness, rigidity, and the arithmetic payload of the spectral free-witness

Adversarial follow-up to `Algebra.SpectralFreeWitness`:

* `heatReturn_injective` — **rigidity**: on the range `r ≤ N` the single heat-kernel
  value determines the order, so `r ↦ p_n(e)` is injective there.
* `heatReturn_approx_multiplicative` — an **honest correction** to the claim that the
  heat-kernel witness is "non-multiplicative": as a *function of the order* the witness
  value is multiplicative up to `1/N²`, since it is `1/r` to that accuracy.  Only the
  *mechanism* (a spectral aggregate) is non-multiplicative, not the witness value.
* `dyadicEigen_mersenne_ge`, `dyadic_gap_isTheta` — **sharpness**: for the Mersenne
  cycle length `r = 2^M - 1` the top nontrivial dyadic eigenvalue is at least
  `1 - 106/(M+1)`, so the spectral gap of the lacunary dyadic walk really is
  `Θ(1/M)`; the `O((log N)²)` mixing time cannot be improved to `O(log N)`
  by this generator set.
* `nontrivial_factor_of_sqrt_one`, `factor_from_even_order` — the **arithmetic
  payload**: a recovered even order with a non-trivial square root of `1` splits `N`.

No `sorry`, no `native_decide`.
-/


open SpectralFreeWitness

open Finset Real

/-! ## 1. Rigidity of the witness -/


/-! ## 2. The witness value is (approximately) multiplicative -/


/-! ## 3. Sharpness of the spectral gap -/



/-! ## 4. Arithmetic payload: a recovered order splits `N` -/




open SpectralFreeWitness in
theorem solution(M : ℕ) (hM : 1 ≤ M) :
    1 - 106 / ((M : ℝ) + 1) ≤ dyadicEigen (2 ^ M - 1) M 1 := by
  have hpow : (1 : ℕ) ≤ 2 ^ M := Nat.one_le_two_pow
  have h2M : (2 : ℝ) ≤ 2 ^ M := by
    have : (2 : ℝ) ^ 1 ≤ 2 ^ M := by
      apply pow_le_pow_right₀ (by norm_num) hM
    simpa using this
  set R : ℝ := ((2 ^ M - 1 : ℕ) : ℝ) with hR
  have hRc : R = (2 : ℝ) ^ M - 1 := by
    rw [hR, Nat.cast_sub hpow]
    push_cast
    ring
  have hRpos : 0 < R := by rw [hRc]; linarith
  have hR2 : (2 : ℝ) ^ M ≤ 2 * R := by rw [hRc]; linarith
  have hRsq : (4 : ℝ) ^ M ≤ 4 * R ^ 2 := by
    have h4 : (4 : ℝ) ^ M = ((2 : ℝ) ^ M) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hpos : (0 : ℝ) < 2 ^ M := by positivity
    nlinarith
  have hpi := Real.pi_pos
  have hpi2 : π ^ 2 ≤ 9.9225 := by
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  -- termwise quadratic lower bound for the cosine
  have hterm : ∀ t ∈ range (M + 1),
      1 - 2 * π ^ 2 * (4 : ℝ) ^ t / R ^ 2
        ≤ Real.cos (2 * π * ((1 * 2 ^ t : ℕ) : ℝ) / R) := by
    intro t _
    have hcos := Real.one_sub_sq_div_two_le_cos (x := 2 * π * ((1 * 2 ^ t : ℕ) : ℝ) / R)
    have hcast : ((1 * 2 ^ t : ℕ) : ℝ) = (2 : ℝ) ^ t := by push_cast; ring
    have hsq : (2 * π * ((1 * 2 ^ t : ℕ) : ℝ) / R) ^ 2 / 2 = 2 * π ^ 2 * (4 : ℝ) ^ t / R ^ 2 := by
      rw [hcast]
      have h4t : ((2 : ℝ) ^ t) ^ 2 = (4 : ℝ) ^ t := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      field_simp
      nlinarith [h4t]
    linarith [hsq ▸ hcos]
  have hsum : ∑ t ∈ range (M + 1), (1 - 2 * π ^ 2 * (4 : ℝ) ^ t / R ^ 2)
      ≤ ∑ t ∈ range (M + 1), Real.cos (2 * π * ((1 * 2 ^ t : ℕ) : ℝ) / R) :=
    Finset.sum_le_sum hterm
  -- evaluate the geometric sum
  have hgeom : ∑ t ∈ range (M + 1), (4 : ℝ) ^ t = ((4 : ℝ) ^ (M + 1) - 1) / 3 := by
    rw [geom_sum_eq (by norm_num)]
    norm_num
  have hleft : ∑ t ∈ range (M + 1), (1 - 2 * π ^ 2 * (4 : ℝ) ^ t / R ^ 2)
      = ((M : ℝ) + 1) - 2 * π ^ 2 * (((4 : ℝ) ^ (M + 1) - 1) / 3) / R ^ 2 := by
    rw [Finset.sum_sub_distrib, ← hgeom]
    congr 1
    · simp
    · rw [← Finset.sum_div, ← Finset.mul_sum]
  have hbound : 2 * π ^ 2 * (((4 : ℝ) ^ (M + 1) - 1) / 3) / R ^ 2 ≤ 106 := by
    have hR2pos : (0 : ℝ) < R ^ 2 := by positivity
    rw [div_le_iff₀ hR2pos]
    have h41 : (4 : ℝ) ^ (M + 1) = 4 * 4 ^ M := by ring
    have hkey : (4 : ℝ) ^ M ≤ 4 * R ^ 2 := hRsq
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 4) M, sq_nonneg π]
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  rw [dyadicEigen, le_div_iff₀ hMpos]
  have hrhs : (1 - 106 / ((M : ℝ) + 1)) * ((M : ℝ) + 1) = ((M : ℝ) + 1) - 106 := by
    field_simp
  rw [hrhs]
  linarith [hsum, hleft, hbound]
