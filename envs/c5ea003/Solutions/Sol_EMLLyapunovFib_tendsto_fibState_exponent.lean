-- Prove2me | solution 1 for EMLLyapunovFib.tendsto_fibState_exponent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:27:27.051318+00:00
-- url     : https://prove2.me/submissions/04989895-4886-4516-97ee-94fe0c2cfdd8

-- Sol generated from Novelty/EMLLyapunovFibonacci.lean
import Mathlib
import Definitions.Def_Novelty_EMLLyapunovFibonacci
import Theorems.Thm_EMLLyapunovFib_tendsto_log_fib

/-!
# Lyapunov Exponents for Recurrent EML Architectures III: the two-tap linear unit

The simplest genuinely recurrent EML architecture with memory depth `2` is the *two-tap
linear recurrent unit*

`h_{t+1} = h_t + h_{t-1}`,

whose one-step state map is the Fibonacci companion matrix `M = !![1, 1; 1, 0]`.
This file computes its maximum Lyapunov exponent **exactly**:

`λ = log φ`,  where `φ = (1 + √5)/2` is the golden ratio,

and derives the two consequences that matter for training such an architecture:

* `log_goldenRatio_pos` — `λ > 0`, so the unnormalised two-tap unit *provably* suffers
  exploding gradients: the state norm grows like `φ^T`.
* `tendsto_normalised_exponent` — rescaling the recurrent weights by `φ⁻¹` puts the
  architecture exactly at the edge of chaos, exponent `0`.

The computation is a bridge between number theory (Binet's formula, the golden ratio) and
recurrent-network dynamics: the exact exponent is a quadratic irrational, and the
`φ`-eigenvector `(φ, 1)` of the companion matrix is the exact unstable direction.

## Main results

* `tendsto_fib_div_goldenRatio_pow` — `fib n / φ ^ n → 1/√5`.
* `tendsto_log_fib` — `(1/n) log (fib n) → log φ` (the exact exponent).
* `fibState_succ`, `norm_fibState` — the two-tap unit's state trajectory and its sup norm.
* `tendsto_fibState_exponent` — the exact maximum Lyapunov exponent of the two-tap unit.
* `fibCompanion_eigenvector` — `(φ, 1)` is the exact unstable eigendirection.
* `tendsto_normalised_exponent` — the `φ⁻¹`-normalised unit has exponent exactly `0`.
-/

open Filter Topology Real
open scoped goldenRatio

open EMLLyapunovFib

/-! ## 1.  Binet asymptotics -/



/-! ## 2.  The exact exponent -/



/-! ## 3.  The state trajectory of the two-tap unit -/




/-- The sup norm of the state is the leading Fibonacci number. -/
theorem norm_fibState (n : ℕ) : ‖fibState n‖ = Nat.fib (n + 1) := by
  have hmono : Nat.fib n ≤ Nat.fib (n + 1) := Nat.fib_le_fib_succ
  have h1 : ‖fibState n‖ ≤ (Nat.fib (n + 1) : ℝ) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)
    fin_cases i <;> simp [fibState]
    exact_mod_cast hmono
  have h2 : (Nat.fib (n + 1) : ℝ) ≤ ‖fibState n‖ := by
    have := norm_le_pi_norm (fibState n) 0
    simpa [fibState] using this
  linarith





open EMLLyapunovFib in
theorem solution:
    Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ‖fibState n‖) Filter.atTop (𝓝 (Real.log φ)) := by
  have hshift : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (Nat.fib (n + 1))) Filter.atTop
      (𝓝 (Real.log φ)) := by
    have hA : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ * Real.log (Nat.fib (n + 1))) Filter.atTop
        (𝓝 (Real.log φ)) := tendsto_log_fib.comp (tendsto_add_atTop_nat 1)
    have hratio : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) Filter.atTop (𝓝 1) := by
      have : ∀ᶠ n : ℕ in Filter.atTop, ((n + 1 : ℕ) : ℝ) / (n : ℝ) = 1 + (n : ℝ)⁻¹ := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
        push_cast
        field_simp
      refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm this) ?_
      have hlim : Filter.Tendsto (fun n : ℕ => (1:ℝ) + (n : ℝ)⁻¹) Filter.atTop (𝓝 ((1:ℝ) + 0)) :=
        tendsto_const_nhds.add tendsto_inv_atTop_nhds_zero_nat
      simpa using hlim
    have hprod := hA.mul hratio
    rw [mul_one] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  refine hshift.congr (fun n => ?_)
  rw [norm_fibState]
