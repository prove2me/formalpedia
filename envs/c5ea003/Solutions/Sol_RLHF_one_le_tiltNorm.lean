-- Prove2me | solution 1 for RLHF.one_le_tiltNorm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:06:19.606657+00:00
-- url     : https://prove2.me/submissions/31e4c95c-774b-430a-b890-fa84a9584656

-- Sol generated from Algebra/RLHFMeanAbsoluteDeviation.lean
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFMeanAbsoluteDeviation
import Theorems.Thm_RLHF_sum_centered

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
omit [Nonempty Ω] in
theorem solution{β : ℝ} {r p : Ω → ℝ} (hp : IsDist p) : 1 ≤ tiltNorm β r p := by
  have hle : ∀ y ∈ (univ : Finset Ω), p y * (1 + (r y - mean p r) / β)
      ≤ p y * Real.exp ((r y - mean p r) / β) := by
    intro y _
    refine mul_le_mul_of_nonneg_left ?_ (hp.nonneg y)
    linarith [Real.add_one_le_exp ((r y - mean p r) / β)]
  have hsum := Finset.sum_le_sum hle
  have hlin : ∑ y, p y * (1 + (r y - mean p r) / β) = 1 := by
    have h : ∀ y, p y * (1 + (r y - mean p r) / β)
        = p y + (1 / β) * (p y * (r y - mean p r)) := fun y => by ring
    rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_centered hp r, hp.total]
    ring
  rw [hlin] at hsum
  exact hsum
