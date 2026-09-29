-- Prove2me | solution 1 for RLHF.sqrt_two_kl_tendsto_stddev
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:30:22.966261+00:00
-- url     : https://prove2.me/submissions/51c59e30-fd74-40e4-9d12-8ade8d1a6604

-- Sol generated from Algebra/RLHFAuditDrift.lean
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFKLSecondOrder
import Theorems.Thm_RLHF_kl_tendsto_half_variance

/-!
# Exact first-order audit drift: the constant is the covariance

Domain: Algebra (convex analysis × information theory × alignment theory).

The catalogue's anti-reward-hacking bound `RLHF.audit_gap_le_stddev` controls the shift
of an audit statistic `f` under alignment by `σ_p(r)·σ_p(f)·e^{range r/β}/β`.  This file
identifies the exact constant: it is the **covariance**

  `β · (𝔼_{π_β} f − 𝔼_p f) → Cov_p(r, f)`.

* `RLHF.audit_gap_eq_centred` — the exact identity
  `𝔼_{π_β} f − 𝔼_p f = 𝔼_p[(e^{(r−𝔼r)/β} − 1)(f − 𝔼_p f)] / W_β`;
* `RLHF.abs_audit_gap_sub_cov` — `|𝔼_{π_β} f − 𝔼_p f − Cov_p(r,f)/β| ≤
  3·range(f)·Var_p(r)/β²` for `β ≥ range r`;
* `RLHF.audit_gap_tendsto_cov` — hence `β(𝔼_{π_β} f − 𝔼_p f) → Cov_p(r,f)`;
* `RLHF.audit_invariant_of_cov_zero` — an audit statistic **uncorrelated with the
  reward cannot be moved to first order**: its drift is `o(β⁻¹)`.  Reward hacking is
  therefore exactly the reward-correlated component of the audit statistic, and the
  `σ_p(r)σ_p(f)` bound is the Cauchy–Schwarz relaxation of this exact law.

The second half of the file closes the loop between the two sharp laws of
`Algebra.RLHFMeanAbsoluteDeviation` (`ℓ¹` drift `→ MAD/β`) and
`Algebra.RLHFKLSecondOrder` (KL drift `→ Var/(2β²)`):

* `RLHF.pinsker_defect_tendsto` — `‖π_β − p‖₁ / √(2 KL(π_β‖p)) → MAD_p(r)/σ_p(r)`;
* `RLHF.pinsker_asymptotically_tight_iff` — the Pinsker inequality is asymptotically
  tight along the Gibbs path **iff** `|r − 𝔼_p r|` is constant, i.e. exactly for the
  balanced two-valued rewards.

So the standard-deviation constant of conjecture C1 is exactly the Pinsker relaxation
of the true constant, and the deficiency is the deviation defect `σ_p(r) − MAD_p(r)`.
-/

open RLHF

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## 1. The exact audit-drift identity -/







/-! ## 2. The exact Pinsker defect along the Gibbs path -/





open RLHF in
theorem solution{r p : Ω → ℝ} (hp : IsPosDist p) :
    Filter.Tendsto (fun β : ℝ => β * Real.sqrt (2 * klDiv (gibbsPolicy β r p) p))
      Filter.atTop (nhds (Real.sqrt (variance p r))) := by
  have hkl := kl_tendsto_half_variance (r := r) hp
  have hmul : Filter.Tendsto (fun β : ℝ => 2 * (β ^ 2 * klDiv (gibbsPolicy β r p) p))
      Filter.atTop (nhds (variance p r)) := by
    have := hkl.const_mul (2 : ℝ)
    have heq : 2 * (variance p r / 2) = variance p r := by ring
    rwa [heq] at this
  have hsqrt : Filter.Tendsto
      (fun β : ℝ => Real.sqrt (2 * (β ^ 2 * klDiv (gibbsPolicy β r p) p))) Filter.atTop
      (nhds (Real.sqrt (variance p r))) := (Real.continuous_sqrt.tendsto _).comp hmul
  refine hsqrt.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with β hβ
  have h1 : 2 * (β ^ 2 * klDiv (gibbsPolicy β r p) p)
      = β ^ 2 * (2 * klDiv (gibbsPolicy β r p) p) := by ring
  rw [h1, Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ.le]
