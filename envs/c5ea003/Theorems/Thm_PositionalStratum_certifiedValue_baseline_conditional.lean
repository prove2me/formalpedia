-- Prove2me | Theorems.Thm_PositionalStratum_certifiedValue_baseline_conditional
-- name    : PositionalStratum.certifiedValue_baseline_conditional
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:59:41.776489+00:00
-- url     : https://prove2.me/theorems/3904aed0-faea-475a-a0e5-706306e7c99c
-- title:
--   Baseline-conditionality of F3.
-- statement:
--   **Baseline-conditionality of F3.**  Against T1a's own `C₀ = (M+1)/2` baseline the very
--   same algorithm is worth strictly less than the certified number, and strictly more than
--   half of it: `S/2 < S_{C₀} < S`.  A value claim is meaningless without naming its
--   baseline.
--
--   ```lean
--   theorem PositionalStratum.certifiedValue_baseline_conditional{M mu P : ℝ} (hM : 1 < M)
--       (hmu : 0 < mu) (hmu1 : mu < 1) (hP : 0 < P) (hP1 : P < 1) :
--       certifiedValue mu P / 2 < descValue M mu P ∧ descValue M mu P < certifiedValue mu P := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/PositionalStratumCertifiedLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/PositionalStratumCertifiedLaw.lean#L90

-- Thm stub generated from Applications/PositionalStratumCertifiedLaw.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumCertifiedLaw
import Definitions.Def_Applications_PositionalStratumMeasure
/-
# The certified positional-stratum value law, its baseline, and the paper-219 erratum

The *simultaneous-commitment* (block) cost model of the positional-stratum framework:
`M` slots are split into a retained stratum `R` of relative size `μ` and its complement.
The algorithm commits to one block before probing, so it pays for the *whole* block it
scans: `μ·M` probes when the target is captured (probability `P`) and `(1-μ)·M` otherwise.
By the r̄-identity of `Applications.PositionalStratumMeasure` (block cost kernel,
`r̄_R = μM`, `r̄_C = (1-μ)M`) the expected cost is

  `EC(μ,P) = M · (μ·P + (1-μ)·(1-P))`,

and the certified value against the **full-scan-`M`** baseline is

  `S(μ,P) = 1 / (μ·P + (1-μ)·(1-P))`.

Results proved here.

* `certifiedValue_of_blockEC` — the law *is* the block-model speedup (derived, not
  posited); `blockEC_eq_rbar_combination` exhibits it as an instance of the r̄-identity.
* `certifiedValue_baseline_conditional`, `baseline_ratio` — **F3 is baseline-conditional**:
  against T1a's own `C₀ = (M+1)/2` baseline the same algorithm is worth strictly less, by
  the exact factor `(M+1)/(2M)`, i.e. asymptotically **half** the certified number.
* `descending_adversary_undercuts` — a same-prior adversary at a neighbouring admissible
  locus realises `5.3648… < 5.4054…`: the certified number is not a locus-free guarantee.
* `feasibility_mu_le_inv_certifiedValue` — the feasibility test `μ ≤ 1/S` holds on the whole
  admissible half-box `μ ≤ 1/2`, so it cannot be flipped by re-reading `P̂`.
* `erratum_row_value`, `erratum_rounded_value`, `erratum_gap` — the recorded row
  `(μ, P̂) = (0.02, 0.9853)` evaluates to `29.3152…`, whereas the printed `29.0698…` is the
  value at the **rounded** `P = 0.985`; `erratum_feasibility_unaffected` shows the
  feasibility verdict is nevertheless identical.
* `certifiedValue_symmetry`, `certifiedValue_swap`, `certifiedValue_gt_one`,
  `certifiedValue_strictMono_in_P` — structure of the law.
-/

open PositionalStratum

noncomputable section

/-! ## The block (simultaneous-commitment) model -/








/-! ## F3 : the value is baseline-conditional -/

theorem PositionalStratum.certifiedValue_baseline_conditional{M mu P : ℝ} (hM : 1 < M)
    (hmu : 0 < mu) (hmu1 : mu < 1) (hP : 0 < P) (hP1 : P < 1) :
    certifiedValue mu P / 2 < descValue M mu P ∧ descValue M mu P < certifiedValue mu P := by sorry
