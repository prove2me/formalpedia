-- Prove2me | Definitions.Def_Logic_JFeatureMaxStatistic
-- name    : Logic_JFeatureMaxStatistic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:54:32.774365+00:00
-- url     : https://prove2.me/theorems/564a7d61-4de1-4f85-9aa6-e42167223095
-- title:
--   Aether Catalog definitions — Logic_JFeatureMaxStatistic
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.JFeatureMaxStatistic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/JFeatureMaxStatistic.lean by skeleton subtraction
import Mathlib
/-
# Max-statistic calibration: why a scan over many cells needs its own null

The j-feature sweep of paper 248 produced a raw maximum of `R = 1.5578`
(cell `j ≡ 73 mod 105`, `n = 1022`, 26 hits) which nevertheless sits *below* the
null distribution's own median max-of-105-ratios (`1.6334`), giving a global
permutation p-value of `0.754`.  This file proves the four facts that make that
inference airtight, in a finite ensemble model.

Let `Ω` be a finite ensemble of null draws (the permutation replicates) and
`T : Ω → ℝ` a statistic.  The one-sided permutation p-value of an observed
value `t` is `pval T t = #{ω : T ω ≥ t} / #Ω`.

* `pval_ge_half_of_le_median` : **the median argument.**  If the observed value
  lies at or below a median of the null statistic, the p-value is at least
  `1/2` — no calibration constant, no distributional assumption.  This is the
  exact inference used to dismiss `R = 1.5578 < 1.6334`.
* `pval_eq_one_of_floor` : **the uncalibrated max test has size 1.**  Since the
  selection floor of `Logic.JFeatureMarginalBlindness` forces every null draw's
  max ratio to be at least `1`, testing "is the max ratio `> 1`?" rejects with
  probability `1` under the null.  Calibration is not optional.
* `pval_max_le_sum_pval` and `bonferroni_valid` : the union bound over cells,
  and the validity of the Bonferroni adjustment `min 1 (K * p)`.
* `perm_pval_valid` : **exact finite-sample validity** of the permutation
  p-value: `#{ω : pval T (T ω) ≤ α} ≤ α * #Ω` for every `α ≥ 0`, with no
  assumption on `T` whatsoever.  This is what licenses the max-statistic
  calibration in the first place.
-/

namespace Logic.JFeature

open Finset

section MaxStatistic

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- One-sided permutation p-value of the observed value `t` for the statistic
`T` evaluated on the null ensemble `Ω`. -/
noncomputable def pval (T : Ω → ℝ) (t : ℝ) : ℝ :=
  ((univ.filter (fun w => t ≤ T w)).card : ℝ) / (Fintype.card Ω : ℝ)

/-- `m` is a median of `T` on the null ensemble. -/
def IsMedian (T : Ω → ℝ) (m : ℝ) : Prop :=
  Fintype.card Ω ≤ 2 * (univ.filter (fun w => m ≤ T w)).card ∧
    Fintype.card Ω ≤ 2 * (univ.filter (fun w => T w ≤ m)).card







/-! ### Scanning many cells: union bound and Bonferroni -/

variable {κ : Type*} [Fintype κ]

/-- The max-of-cells statistic. -/
noncomputable def maxStat (T : κ → Ω → ℝ) (hκ : (univ : Finset κ).Nonempty) (w : Ω) : ℝ :=
  (univ : Finset κ).sup' hκ (fun c => T c w)



/-! ### Exact finite-sample validity of the permutation p-value -/



end MaxStatistic

end Logic.JFeature


