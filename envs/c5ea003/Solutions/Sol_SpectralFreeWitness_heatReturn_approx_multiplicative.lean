-- Prove2me | solution 1 for SpectralFreeWitness.heatReturn_approx_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:50:48.701953+00:00
-- url     : https://prove2.me/submissions/60d45d33-ab61-4f59-9266-21c971d99223

-- Sol generated from Speculative/AutoResearch/SpectralFreeWitnessSharp.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
import Theorems.Thm_SpectralFreeWitness_beta_pow_le
import Theorems.Thm_SpectralFreeWitness_heatReturn_lower
import Theorems.Thm_SpectralFreeWitness_heatReturn_upper
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
theorem solution(N M r₁ r₂ : ℕ) (h1 : 0 < r₁) (h2 : 0 < r₂)
    (hr1 : r₁ ≤ N) (hr2 : r₂ ≤ N) (hprod : r₁ * r₂ ≤ N) (hM : N ≤ 2 ^ M) :
    |heatReturn (r₁ * r₂) M (8 * (M + 1) ^ 2)
      - heatReturn r₁ M (8 * (M + 1) ^ 2) * heatReturn r₂ M (8 * (M + 1) ^ 2)|
      ≤ 1 / (N : ℝ) ^ 2 := by
  have hN : 0 < N := lt_of_lt_of_le h1 hr1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < r₁ * r₂ := Nat.mul_pos h1 h2
  set n := 8 * (M + 1) ^ 2 with hn
  set ε : ℝ := 1 / (4 * (N : ℝ) ^ 2) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hmix := beta_pow_le N M hN hM
  -- three instances of the two-sided estimate
  have key : ∀ r : ℕ, 0 < r → r ≤ N →
      1 / (r : ℝ) ≤ heatReturn r M n ∧ heatReturn r M n ≤ 1 / (r : ℝ) + ε := by
    intro r hr hrN
    refine ⟨heatReturn_lower r M n hr, ?_⟩
    have := heatReturn_upper r M n hr (le_trans hrN hM)
    linarith
  obtain ⟨l1, u1⟩ := key r₁ h1 hr1
  obtain ⟨l2, u2⟩ := key r₂ h2 hr2
  obtain ⟨lp, up⟩ := key (r₁ * r₂) hp hprod
  have hc1 : (0 : ℝ) < r₁ := by exact_mod_cast h1
  have hc2 : (0 : ℝ) < r₂ := by exact_mod_cast h2
  have hr1' : (r₁ : ℝ) ≤ N := by exact_mod_cast hr1
  have hr2' : (r₂ : ℝ) ≤ N := by exact_mod_cast hr2
  have hcp : ((r₁ * r₂ : ℕ) : ℝ) = (r₁ : ℝ) * r₂ := by push_cast; ring
  have hone1 : 1 / (r₁ : ℝ) ≤ 1 := by
    rw [div_le_one hc1]; exact_mod_cast h1
  have hone2 : 1 / (r₂ : ℝ) ≤ 1 := by
    rw [div_le_one hc2]; exact_mod_cast h2
  have hεle : ε ≤ 1 / (4 * (N : ℝ) ^ 2) := le_of_eq hε
  have h1N : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hεsmall : ε ≤ 1 / 4 := by
    rw [hε]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  -- products
  have hprodlow : 1 / (r₁ : ℝ) * (1 / (r₂ : ℝ)) ≤ heatReturn r₁ M n * heatReturn r₂ M n := by
    have hnn2 : (0 : ℝ) ≤ 1 / (r₂ : ℝ) := by positivity
    have hnn1 : (0 : ℝ) ≤ heatReturn r₁ M n := le_trans (by positivity) l1
    exact mul_le_mul l1 l2 hnn2 hnn1
  have hpu : heatReturn r₁ M n * heatReturn r₂ M n
      ≤ 1 / (r₁ : ℝ) * (1 / (r₂ : ℝ)) + 3 * ε := by
    have hstep : heatReturn r₁ M n * heatReturn r₂ M n
        ≤ (1 / (r₁ : ℝ) + ε) * (1 / (r₂ : ℝ) + ε) :=
      mul_le_mul u1 u2 (le_trans (by positivity) l2) (by positivity)
    nlinarith [hone1, hone2, hεsmall, hεpos]
  rw [abs_le]
  rw [hcp] at lp up
  have hfac : 1 / ((r₁ : ℝ) * r₂) = 1 / (r₁ : ℝ) * (1 / (r₂ : ℝ)) := by
    field_simp
  rw [hfac] at lp up
  have h4 : 4 * ε = 1 / (N : ℝ) ^ 2 := by
    rw [hε]; field_simp
  constructor
  · linarith
  · linarith
