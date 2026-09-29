-- Prove2me | solution 1 for RLHF.abs_l1_numerator_sub_mad
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:22:19.320429+00:00
-- url     : https://prove2.me/submissions/0f40deb3-1c2c-492f-81c9-e9ac95dc8965

-- Sol generated from Algebra/RLHFMeanAbsoluteDeviation.lean
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFMeanAbsoluteDeviation
import Theorems.Thm_RLHF_abs_sub_mean_le_range
import Theorems.Thm_RLHF_one_le_tiltNorm
import Theorems.Thm_RLHF_tiltNorm_le

/-!
# The sharp alignment-drift constant is the mean absolute deviation

Domain: Algebra (convex analysis × information theory × alignment theory).

Conjecture **C1** of the drift thread said that the constant in the `Θ(β⁻¹)` alignment
drift law `‖π_β − p‖₁ ≲ c/β` is the reward *standard deviation* `σ_p(r)`, refining the
earlier reward-*range* constant; the catalogue proves
`‖π_β − p‖₁ ≤ √(2 e^{range r/β} Var_p r)/β` and sandwiches an explicit family between
`σ/(2β)` and `3σ/β`.  What was left open was **the absolute constant**.

This file settles it, and the answer is *not* `σ_p(r)`.  The exact first-order drift
constant is the **mean absolute deviation**

  `MAD_p(r) = 𝔼_p |r − 𝔼_p r| ≤ σ_p(r)`,

with a *quantitative, non-asymptotic* two-sided estimate valid as soon as the
temperature exceeds the reward range:

* `RLHF.l1_drift_upper_mad` — `‖π_β − p‖₁ ≤ MAD_p(r)/β + 2 Var_p(r)/β²`;
* `RLHF.l1_drift_lower_mad` — `‖π_β − p‖₁ ≥ MAD_p(r)/β − 3 Var_p(r)/β²`;
* `RLHF.l1_drift_tendsto_mad` — hence `β·‖π_β − p‖₁ → MAD_p(r)` as `β → ∞`, so the
  constant `1` is attained by `MAD` and by no smaller functional.

The comparison with C1 is exact, via the *deviation defect identity*
`Var_p(r) − MAD_p(r)² = 𝔼_p(|r − 𝔼r| − MAD)²`:

* `RLHF.mad_le_sqrt_variance` — `MAD_p(r) ≤ σ_p(r)` always, so the σ-law of C1 is
  never violated;
* `RLHF.mad_eq_sqrt_variance_iff` — equality holds **iff** `|r − 𝔼_p r|` is constant,
  i.e. exactly for the balanced two-valued rewards.  This explains why the two-point
  family of `RLHF.variance_constant_optimal` saturated the σ-law: it is the unique
  saturating shape.
* `RLHF.mad_sq_spike_eq` — on the rare-spike family `p(true) = ε`, `r = 1_{true}`,
  `MAD² = 4ε(1−ε)·Var`, so the σ-constant is off by the unbounded factor
  `1/(2√(ε(1−ε)))`: the MAD law is *strictly*, and unboundedly, sharper.

The proof is a centred second-order expansion of the exponential tilt: writing
`u = r − 𝔼_p r`, `s = u/β` and `W = 𝔼_p e^{s}`, one has `π_β = p e^{s}/W`, `W ≥ 1` by
Jensen, `W ≤ 1 + Var/β²` by the quadratic Taylor bound `|e^x − 1 − x| ≤ x²` for
`|x| ≤ 1`, and the triangle inequality transfers `|e^{s} − W| ≈ |s|` termwise.
-/

open RLHF

open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## 1. The deviation defect identity: `MAD ≤ σ` and its equality case -/





variable [Nonempty Ω]


/-! ## 2. The centred tilt normaliser -/





/-! ## 3. The Gibbs policy in centred form -/




/-! ## 4. The sharp two-sided drift law -/





/-! ## 5. Separation from the standard-deviation law: the rare-spike family -/










open RLHF in
theorem solution{β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsDist p)
    (hr : rewardRange r ≤ β) :
    abs ((∑ y, p y * |Real.exp ((r y - mean p r) / β) - tiltNorm β r p|) - mad p r / β)
      ≤ 2 * (variance p r / β ^ 2) := by
  have hsmall : ∀ y, |(r y - mean p r) / β| ≤ 1 := by
    intro y
    rw [abs_div, abs_of_pos hβ, div_le_one hβ]
    exact le_trans (abs_sub_mean_le_range hp y) hr
  have hW1 := one_le_tiltNorm (β := β) (r := r) hp
  have hW2 := tiltNorm_le (β := β) (r := r) hβ hp hr
  have hmadeq : mad p r / β = ∑ y, p y * |(r y - mean p r) / β| := by
    rw [mad, Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [abs_div, abs_of_pos hβ]
    ring
  rw [hmadeq, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ y ∈ (univ : Finset Ω),
      abs (p y * |Real.exp ((r y - mean p r) / β) - tiltNorm β r p|
        - p y * |(r y - mean p r) / β|)
      ≤ p y * (((r y - mean p r) / β) ^ 2 + variance p r / β ^ 2) := by
    intro y _
    set s := (r y - mean p r) / β with hs
    have htri : abs (|Real.exp s - tiltNorm β r p| - |s|)
        ≤ |Real.exp s - tiltNorm β r p - s| := abs_abs_sub_abs_le_abs_sub _ _
    have hsplit : |Real.exp s - tiltNorm β r p - s|
        ≤ |Real.exp s - 1 - s| + |tiltNorm β r p - 1| := by
      rw [show Real.exp s - tiltNorm β r p - s
          = (Real.exp s - 1 - s) - (tiltNorm β r p - 1) by ring]
      exact abs_sub _ _
    have h1 : |Real.exp s - 1 - s| ≤ s ^ 2 := Real.abs_exp_sub_one_sub_id_le (hsmall y)
    have h2 : |tiltNorm β r p - 1| ≤ variance p r / β ^ 2 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hcomb : abs (|Real.exp s - tiltNorm β r p| - |s|)
        ≤ s ^ 2 + variance p r / β ^ 2 := by linarith
    calc abs (p y * |Real.exp s - tiltNorm β r p| - p y * |s|)
        = p y * abs (|Real.exp s - tiltNorm β r p| - |s|) := by
          rw [← mul_sub, abs_mul, abs_of_nonneg (hp.nonneg y)]
      _ ≤ p y * (s ^ 2 + variance p r / β ^ 2) :=
          mul_le_mul_of_nonneg_left hcomb (hp.nonneg y)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hrhs : ∑ y, p y * (((r y - mean p r) / β) ^ 2 + variance p r / β ^ 2)
      = variance p r / β ^ 2 + variance p r / β ^ 2 := by
    have h : ∀ y, p y * (((r y - mean p r) / β) ^ 2 + variance p r / β ^ 2)
        = (1 / β ^ 2) * (p y * (r y - mean p r) ^ 2) + (variance p r / β ^ 2) * p y := by
      intro y; ring
    rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hp.total]
    simp only [variance]
    ring
  rw [hrhs]
  linarith
