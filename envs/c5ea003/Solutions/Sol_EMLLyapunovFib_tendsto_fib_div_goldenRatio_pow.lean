-- Prove2me | solution 1 for EMLLyapunovFib.tendsto_fib_div_goldenRatio_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:23:39.945652+00:00
-- url     : https://prove2.me/submissions/fbbd98a0-37d6-4e4d-b86b-78625fbc84ee

-- Sol generated from Novelty/EMLLyapunovFibonacci.lean
import Mathlib
import Definitions.Def_Novelty_EMLLyapunovFibonacci

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

lemma abs_goldenConj_div_goldenRatio_lt_one : |ψ / φ| < 1 := by
  rw [abs_div, div_lt_one (by positivity)]
  have h1 : |ψ| < 1 := by
    rw [abs_lt]
    exact ⟨neg_one_lt_goldenConj, lt_trans goldenConj_neg zero_lt_one⟩
  have h2 : (1:ℝ) < φ := one_lt_goldenRatio
  rw [abs_of_pos goldenRatio_pos]
  linarith


/-! ## 2.  The exact exponent -/



/-! ## 3.  The state trajectory of the two-tap unit -/









open EMLLyapunovFib in
theorem solution:
    Filter.Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / φ ^ n) Filter.atTop (𝓝 (1 / √5)) := by
  have hφ : (0:ℝ) < φ := goldenRatio_pos
  have hEq : ∀ n : ℕ, (Nat.fib n : ℝ) / φ ^ n = (1 - (ψ / φ) ^ n) / √5 := by
    intro n
    have hpow : (φ:ℝ) ^ n ≠ 0 := by positivity
    have hdp : (ψ / φ) ^ n = ψ ^ n / φ ^ n := div_pow ψ φ n
    rw [Real.coe_fib_eq, div_right_comm]
    congr 1
    rw [hdp, sub_div, div_self hpow]
  have h0 : Filter.Tendsto (fun n : ℕ => (ψ / φ) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one abs_goldenConj_div_goldenRatio_lt_one
  have : Filter.Tendsto (fun n : ℕ => (1 - (ψ / φ) ^ n) / √5) Filter.atTop (𝓝 ((1 - 0) / √5)) :=
    ((tendsto_const_nhds.sub h0).div_const _)
  simpa [hEq, sub_zero] using this
