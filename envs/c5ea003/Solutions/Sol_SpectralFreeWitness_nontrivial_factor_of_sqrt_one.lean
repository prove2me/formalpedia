-- Prove2me | solution 1 for SpectralFreeWitness.nontrivial_factor_of_sqrt_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:13:25.710665+00:00
-- url     : https://prove2.me/submissions/80425873-6040-44ad-80aa-c50109bb9c49

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
theorem solution(N : ℕ) (x : ℤ) (hN : 2 ≤ N)
    (hsq : (N : ℤ) ∣ (x - 1) * (x + 1)) (h1 : ¬ (N : ℤ) ∣ (x - 1))
    (h2 : ¬ (N : ℤ) ∣ (x + 1)) :
    Int.gcd (x - 1) (N : ℤ) ∣ N ∧ 1 < Int.gcd (x - 1) (N : ℤ) ∧
      Int.gcd (x - 1) (N : ℤ) < N := by
  set d : ℕ := Int.gcd (x - 1) (N : ℤ) with hd
  have hdvdN : d ∣ N := by
    have : (d : ℤ) ∣ (N : ℤ) := Int.gcd_dvd_right _ _
    exact_mod_cast this
  have hdvdx : (d : ℤ) ∣ (x - 1) := Int.gcd_dvd_left _ _
  have hdne1 : d ≠ 1 := by
    intro h
    have hcop : IsCoprime (x - 1) (N : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by rw [← hd, h])
    exact h2 (hcop.symm.dvd_of_dvd_mul_left hsq)
  have hdneN : d ≠ N := by
    intro h
    apply h1
    rw [← h]
    exact hdvdx
  have hdne0 : d ≠ 0 := by
    intro h
    rw [hd, Int.gcd_eq_zero_iff] at h
    have : (N : ℤ) = 0 := h.2
    have : N = 0 := by exact_mod_cast this
    omega
  have hdleN : d ≤ N := Nat.le_of_dvd (by omega) hdvdN
  exact ⟨hdvdN, by omega, by omega⟩
