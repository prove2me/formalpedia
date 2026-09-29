-- Prove2me | solution 1 for RLHF.audit_gap_tendsto_cov
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:22:19.870599+00:00
-- url     : https://prove2.me/submissions/0c29c7af-df21-4ccc-a890-0be3874f3d19

-- Sol generated from Algebra/RLHFAuditDrift.lean
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFKLSecondOrder
import Theorems.Thm_RLHF_abs_audit_gap_sub_cov

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
theorem solution{r p : Ω → ℝ} (hp : IsPosDist p) (f : Ω → ℝ) :
    Filter.Tendsto (fun β : ℝ => β * (mean (gibbsPolicy β r p) f - mean p f)) Filter.atTop
      (nhds (cov p r f)) := by
  have hinv : Filter.Tendsto (fun β : ℝ => (1 : ℝ) / β) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  have herr : Filter.Tendsto
      (fun β : ℝ => 3 * (rewardRange f * variance p r) * (1 / β)) Filter.atTop (nhds 0) := by
    simpa using hinv.const_mul (3 * (rewardRange f * variance p r))
  have hlow : Filter.Tendsto
      (fun β : ℝ => cov p r f - 3 * (rewardRange f * variance p r) * (1 / β)) Filter.atTop
      (nhds (cov p r f)) := by simpa using tendsto_const_nhds.sub herr
  have hhigh : Filter.Tendsto
      (fun β : ℝ => cov p r f + 3 * (rewardRange f * variance p r) * (1 / β)) Filter.atTop
      (nhds (cov p r f)) := by simpa using tendsto_const_nhds.add herr
  have hsandwich : ∀ β : ℝ, max (rewardRange r) 1 ≤ β →
      |β * (mean (gibbsPolicy β r p) f - mean p f) - cov p r f|
        ≤ 3 * (rewardRange f * variance p r) * (1 / β) := by
    intro β hβm
    have hβ : 0 < β := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hβm)
    have hr : rewardRange r ≤ β := le_trans (le_max_left _ _) hβm
    have hkey := abs_audit_gap_sub_cov hβ hp hr f
    have heq : β * (mean (gibbsPolicy β r p) f - mean p f - cov p r f / β)
        = β * (mean (gibbsPolicy β r p) f - mean p f) - cov p r f := by
      field_simp
    have habs : |β * (mean (gibbsPolicy β r p) f - mean p f - cov p r f / β)|
        = β * |mean (gibbsPolicy β r p) f - mean p f - cov p r f / β| := by
      rw [abs_mul, abs_of_pos hβ]
    rw [← heq, habs]
    refine le_trans (mul_le_mul_of_nonneg_left hkey hβ.le) (le_of_eq ?_)
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (max (rewardRange r) 1)] with β hβm
    linarith [(abs_le.1 (hsandwich β hβm)).1]
  · filter_upwards [Filter.eventually_ge_atTop (max (rewardRange r) 1)] with β hβm
    linarith [(abs_le.1 (hsandwich β hβm)).2]
