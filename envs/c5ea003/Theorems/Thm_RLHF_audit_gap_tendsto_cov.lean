-- Prove2me | Theorems.Thm_RLHF_audit_gap_tendsto_cov
-- name    : RLHF.audit_gap_tendsto_cov
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:54:49.320428+00:00
-- url     : https://prove2.me/theorems/45ade2c2-e0ab-4c63-a249-8822bc20d83f
-- title:
--   The audit-drift limit law.
-- statement:
--   **The audit-drift limit law.**  `β·(𝔼_{π_β} f − 𝔼_p f) → Cov_p(r, f)`.
--
--   ```lean
--   theorem RLHF.audit_gap_tendsto_cov{r p : Ω → ℝ} (hp : IsPosDist p) (f : Ω → ℝ) :
--       Filter.Tendsto (fun β : ℝ => β * (mean (gibbsPolicy β r p) f - mean p f)) Filter.atTop
--         (nhds (cov p r f)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/RLHFAuditDrift.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/RLHFAuditDrift.lean#L191

-- Thm stub generated from Algebra/RLHFAuditDrift.lean
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFKLSecondOrder

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

theorem RLHF.audit_gap_tendsto_cov{r p : Ω → ℝ} (hp : IsPosDist p) (f : Ω → ℝ) :
    Filter.Tendsto (fun β : ℝ => β * (mean (gibbsPolicy β r p) f - mean p f)) Filter.atTop
      (nhds (cov p r f)) := by sorry
