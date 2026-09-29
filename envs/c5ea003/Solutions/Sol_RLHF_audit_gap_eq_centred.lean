-- Prove2me | solution 1 for RLHF.audit_gap_eq_centred
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:03:25.376326+00:00
-- url     : https://prove2.me/submissions/09f91caf-cf47-4643-87e1-0745b9224a36

-- Sol generated from Algebra/RLHFAuditDrift.lean
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFKLSecondOrder
import Definitions.Def_Algebra_RLHFMeanAbsoluteDeviation
import Theorems.Thm_RLHF_gibbsPolicy_eq_centred
import Theorems.Thm_RLHF_tiltNorm_pos

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
theorem solution{β : ℝ} {r p : Ω → ℝ} (hp : IsPosDist p) (f : Ω → ℝ) :
    mean (gibbsPolicy β r p) f - mean p f
      = (∑ y, p y * ((Real.exp ((r y - mean p r) / β) - 1) * (f y - mean p f)))
        / tiltNorm β r p := by
  have hW := tiltNorm_pos (β := β) (r := r) hp
  have hWne : tiltNorm β r p ≠ 0 := ne_of_gt hW
  have hnum : (∑ y, p y * ((Real.exp ((r y - mean p r) / β) - 1) * (f y - mean p f)))
      = (∑ y, p y * (Real.exp ((r y - mean p r) / β) * f y))
        - mean p f * tiltNorm β r p := by
    have h : ∀ y, p y * ((Real.exp ((r y - mean p r) / β) - 1) * (f y - mean p f))
        = p y * (Real.exp ((r y - mean p r) / β) * f y)
          - mean p f * (p y * Real.exp ((r y - mean p r) / β))
          - p y * f y + mean p f * p y := fun y => by ring
    rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.total]
    simp only [tiltNorm, mean]
    ring
  have hmean : mean (gibbsPolicy β r p) f
      = (∑ y, p y * (Real.exp ((r y - mean p r) / β) * f y)) / tiltNorm β r p := by
    rw [mean, Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [gibbsPolicy_eq_centred]
    field_simp
  rw [hmean, hnum]
  field_simp
