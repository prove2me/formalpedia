-- Prove2me | Definitions.Def_Applications_PositionalStratumCertifiedLaw
-- name    : Applications_PositionalStratumCertifiedLaw
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:33.480347+00:00
-- url     : https://prove2.me/theorems/ff30fb53-2881-4d7f-a666-f29217d6e686
-- title:
--   Aether Catalog definitions — Applications_PositionalStratumCertifiedLaw
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.PositionalStratumCertifiedLaw`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/PositionalStratumCertifiedLaw.lean by skeleton subtraction
import Mathlib
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

namespace PositionalStratum

noncomputable section

/-! ## The block (simultaneous-commitment) model -/

/-- Expected cost of the simultaneous-commitment algorithm on `M` slots with retained
fraction `μ` and capture probability `P`. -/
def blockEC (M : ℝ) (mu P : ℝ) : ℝ := M * (mu * P + (1 - mu) * (1 - P))

/-- The certified value law, stated against the full-scan-`M` baseline. -/
def certifiedValue (mu P : ℝ) : ℝ := 1 / (mu * P + (1 - mu) * (1 - P))

/-- The value of the same algorithm against T1a's own baseline `C₀ = (M+1)/2`. -/
def descValue (M : ℝ) (mu P : ℝ) : ℝ := ((M + 1) / 2) / blockEC M mu P





/-! ## F3 : the value is baseline-conditional -/



/-! ## A same-prior adversary undercuts the certified number -/


/-! ## Feasibility is insensitive to the rounding of `P̂` -/


/-! ## The paper-219 witness-table erratum -/






/-! ## Structure of the certified law -/





end

end PositionalStratum


