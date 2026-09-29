-- Prove2me | solution 1 for PositionalStratum.certifiedValue_baseline_conditional
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:59:11.333556+00:00
-- url     : https://prove2.me/submissions/8beaad56-f715-4c43-b992-8f32b79c593c

-- Sol generated from Applications/PositionalStratumCertifiedLaw.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumCertifiedLaw
import Definitions.Def_Applications_PositionalStratumMeasure
import Theorems.Thm_PositionalStratum_denom_pos
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





lemma certifiedValue_pos {mu P : ℝ} (hmu : 0 < mu) (hmu1 : mu < 1) (hP : 0 < P)
    (hP1 : P < 1) : 0 < certifiedValue mu P := by
  rw [certifiedValue]
  exact one_div_pos.mpr (denom_pos hmu hmu1 hP hP1)



/-! ## F3 : the value is baseline-conditional -/

/-- The exact ratio between the two baselines: the certified value overstates the
`C₀ = (M+1)/2`-relative value by the factor `2M/(M+1)`, which tends to `2`. -/
theorem baseline_ratio {M mu P : ℝ} (hM : 0 < M)
    (hmu : 0 < mu) (hmu1 : mu < 1) (hP : 0 < P) (hP1 : P < 1) :
    descValue M mu P = certifiedValue mu P * ((M + 1) / (2 * M)) := by
  have hd := denom_pos hmu hmu1 hP hP1
  have hMne : M ≠ 0 := ne_of_gt hM
  rw [descValue, certifiedValue, blockEC]
  field_simp


/-! ## A same-prior adversary undercuts the certified number -/


/-! ## Feasibility is insensitive to the rounding of `P̂` -/


/-! ## The paper-219 witness-table erratum -/






/-! ## Structure of the certified law -/







open PositionalStratum in
theorem solution{M mu P : ℝ} (hM : 1 < M)
    (hmu : 0 < mu) (hmu1 : mu < 1) (hP : 0 < P) (hP1 : P < 1) :
    certifiedValue mu P / 2 < descValue M mu P ∧ descValue M mu P < certifiedValue mu P := by
  have hMpos : (0 : ℝ) < M := by linarith
  have hv : 0 < certifiedValue mu P := certifiedValue_pos hmu hmu1 hP hP1
  have hratio := baseline_ratio hMpos hmu hmu1 hP hP1
  have hlt1 : (M + 1) / (2 * M) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hgt : (1 : ℝ) / 2 < (M + 1) / (2 * M) := by
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    linarith
  constructor
  · rw [hratio, div_eq_mul_one_div, mul_comm (certifiedValue mu P) (1 / 2)]
    calc 1 / 2 * certifiedValue mu P
        < ((M + 1) / (2 * M)) * certifiedValue mu P := by
          exact mul_lt_mul_of_pos_right hgt hv
      _ = certifiedValue mu P * ((M + 1) / (2 * M)) := by ring
  · rw [hratio]
    calc certifiedValue mu P * ((M + 1) / (2 * M))
        < certifiedValue mu P * 1 := by exact mul_lt_mul_of_pos_left hlt1 hv
      _ = certifiedValue mu P := by ring
