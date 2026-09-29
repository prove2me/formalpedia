-- Prove2me | solution 1 for EMLLyapunovFib.tendsto_log_fib
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:25:57.167678+00:00
-- url     : https://prove2.me/submissions/aff28d7b-3d74-4e66-8642-bd899699355f

-- Sol generated from Novelty/EMLLyapunovFibonacci.lean
import Mathlib
import Definitions.Def_Novelty_EMLLyapunovFibonacci
import Theorems.Thm_EMLLyapunovFib_tendsto_fib_div_goldenRatio_pow

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









open EMLLyapunovFib in
theorem solution:
    Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (Nat.fib n)) Filter.atTop (𝓝 (Real.log φ)) := by
  have hφ : (0:ℝ) < φ := goldenRatio_pos
  have hs : (0:ℝ) < 1 / √5 := by positivity
  have hB : Filter.Tendsto (fun n : ℕ => Real.log ((Nat.fib n : ℝ) / φ ^ n)) Filter.atTop
      (𝓝 (Real.log (1 / √5))) :=
    (Real.continuousAt_log (ne_of_gt hs)).tendsto.comp tendsto_fib_div_goldenRatio_pow
  have hinv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hC : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log ((Nat.fib n : ℝ) / φ ^ n)) Filter.atTop (𝓝 0) := by
    simpa using hinv.mul hB
  have hgoal : Filter.Tendsto (fun n : ℕ => Real.log φ + (n : ℝ)⁻¹ * Real.log ((Nat.fib n : ℝ) / φ ^ n))
      Filter.atTop (𝓝 (Real.log φ + 0)) := tendsto_const_nhds.add hC
  rw [add_zero] at hgoal
  refine hgoal.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hfib : (0:ℝ) < Nat.fib n := by
    exact_mod_cast Nat.fib_pos.mpr hn
  have hpow : (0:ℝ) < φ ^ n := by positivity
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [Real.log_div (ne_of_gt hfib) (ne_of_gt hpow), Real.log_pow]
  field_simp
  ring
