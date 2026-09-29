-- Prove2me | solution 1 for RLHF.gibbsPolicy_eq_centred
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:00:45.982352+00:00
-- url     : https://prove2.me/submissions/ab1fa1d8-b3fb-478d-8ff1-8bd5bc376c44

-- Sol generated from Algebra/RLHFMeanAbsoluteDeviation.lean
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFMeanAbsoluteDeviation

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

omit [Nonempty Ω] in
theorem partition_eq_tiltNorm {β : ℝ} {r p : Ω → ℝ} :
    partition β r p = Real.exp (mean p r / β) * tiltNorm β r p := by
  rw [partition, tiltNorm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← mul_assoc, mul_comm (Real.exp (mean p r / β)) (p y), mul_assoc, ← Real.exp_add,
    show mean p r / β + (r y - mean p r) / β = r y / β by ring]



/-! ## 4. The sharp two-sided drift law -/





/-! ## 5. Separation from the standard-deviation law: the rare-spike family -/










open RLHF in
omit [Nonempty Ω] in
theorem solution{β : ℝ} {r p : Ω → ℝ} (y : Ω) :
    gibbsPolicy β r p y = p y * Real.exp ((r y - mean p r) / β) / tiltNorm β r p := by
  have hexp : Real.exp (r y / β)
      = Real.exp (mean p r / β) * Real.exp ((r y - mean p r) / β) := by
    rw [← Real.exp_add, show mean p r / β + (r y - mean p r) / β = r y / β by ring]
  have h0 : Real.exp (mean p r / β) ≠ 0 := ne_of_gt (Real.exp_pos _)
  rw [gibbsPolicy, partition_eq_tiltNorm, hexp,
    show p y * (Real.exp (mean p r / β) * Real.exp ((r y - mean p r) / β))
      = Real.exp (mean p r / β) * (p y * Real.exp ((r y - mean p r) / β)) by ring,
    mul_div_mul_left _ _ h0]
