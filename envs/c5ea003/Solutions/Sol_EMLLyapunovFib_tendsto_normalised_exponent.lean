-- Prove2me | solution 1 for EMLLyapunovFib.tendsto_normalised_exponent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:30:06.628701+00:00
-- url     : https://prove2.me/submissions/e491dbc2-925f-457e-86ca-0df1c2f04a6b

-- Sol generated from Novelty/EMLLyapunovFibonacci.lean
import Mathlib
import Definitions.Def_Novelty_EMLLyapunovFibonacci
import Theorems.Thm_EMLLyapunovFib_tendsto_fibState_exponent

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
    Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (‖fibState n‖ / φ ^ n)) Filter.atTop (𝓝 0) := by
  have hφ : (0:ℝ) < φ := goldenRatio_pos
  have hmain := tendsto_fibState_exponent
  have hsplit : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ)⁻¹ * Real.log (‖fibState n‖ / φ ^ n)
        = (n : ℝ)⁻¹ * Real.log ‖fibState n‖ - Real.log φ := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hfib : (0:ℝ) < ‖fibState n‖ := by
      rw [norm_fibState]
      exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)
    have hpow : (0:ℝ) < φ ^ n := by positivity
    rw [Real.log_div (ne_of_gt hfib) (ne_of_gt hpow), Real.log_pow]
    field_simp
  refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm hsplit) ?_
  have := hmain.sub (tendsto_const_nhds (x := Real.log φ) (f := Filter.atTop))
  simpa using this
