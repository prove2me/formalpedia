-- Prove2me | solution 1 for RLHF.abs_audit_num_sub_cov
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:00:43.485381+00:00
-- url     : https://prove2.me/submissions/e00fb06e-f577-4815-8727-04a5c09f436d

-- Sol generated from Algebra/RLHFAuditDrift.lean
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFKLSecondOrder
import Theorems.Thm_RLHF_abs_sub_mean_le_range
import Theorems.Thm_RLHF_sum_ctr_sq_div

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

omit [Nonempty Ω] in
/-- The covariance as a centred-reward sum. -/
theorem cov_eq_sum_ctr {p r f : Ω → ℝ} :
    cov p r f = ∑ y, p y * ((r y - mean p r) * (f y - mean p f)) := rfl






/-! ## 2. The exact Pinsker defect along the Gibbs path -/





open RLHF in
theorem solution{β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsDist p)
    (hr : rewardRange r ≤ β) (f : Ω → ℝ) :
    |(∑ y, p y * ((Real.exp ((r y - mean p r) / β) - 1) * (f y - mean p f)))
        - cov p r f / β|
      ≤ rewardRange f * (variance p r / β ^ 2) := by
  have hsmall : ∀ y, |(r y - mean p r) / β| ≤ 1 := by
    intro y
    rw [abs_div, abs_of_pos hβ, div_le_one hβ]
    exact le_trans (abs_sub_mean_le_range hp y) hr
  have hcov : cov p r f / β = ∑ y, p y * (((r y - mean p r) / β) * (f y - mean p f)) := by
    rw [cov_eq_sum_ctr, Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [hcov, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ y ∈ (univ : Finset Ω),
      |p y * ((Real.exp ((r y - mean p r) / β) - 1) * (f y - mean p f))
        - p y * (((r y - mean p r) / β) * (f y - mean p f))|
      ≤ rewardRange f * (p y * ((r y - mean p r) / β) ^ 2) := by
    intro y _
    set s := (r y - mean p r) / β with hs
    have htaylor : |Real.exp s - 1 - s| ≤ s ^ 2 := Real.abs_exp_sub_one_sub_id_le (hsmall y)
    have hg : |f y - mean p f| ≤ rewardRange f := abs_sub_mean_le_range hp y
    have heq : p y * ((Real.exp s - 1) * (f y - mean p f))
        - p y * (s * (f y - mean p f))
        = p y * ((Real.exp s - 1 - s) * (f y - mean p f)) := by ring
    rw [heq, abs_mul, abs_of_nonneg (hp.nonneg y), abs_mul]
    have hprod : |Real.exp s - 1 - s| * |f y - mean p f| ≤ s ^ 2 * rewardRange f :=
      mul_le_mul htaylor hg (abs_nonneg _) (sq_nonneg s)
    calc p y * (|Real.exp s - 1 - s| * |f y - mean p f|)
        ≤ p y * (s ^ 2 * rewardRange f) := mul_le_mul_of_nonneg_left hprod (hp.nonneg y)
      _ = rewardRange f * (p y * s ^ 2) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum, sum_ctr_sq_div]
