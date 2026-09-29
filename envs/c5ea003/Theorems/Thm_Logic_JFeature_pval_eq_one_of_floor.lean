-- Prove2me | Theorems.Thm_Logic_JFeature_pval_eq_one_of_floor
-- name    : Logic.JFeature.pval_eq_one_of_floor
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:30:07.697349+00:00
-- url     : https://prove2.me/theorems/c6e6aa8a-5826-440f-b9d5-60c38737a7a3
-- title:
--   The uncalibrated max test has size one.
-- statement:
--   **The uncalibrated max test has size one.**  If every null draw already
--   produces a statistic at least `1` — which the pigeonhole selection floor
--   guarantees for max-of-cells enrichment ratios — then the threshold `1` rejects
--   on the entire null ensemble.
--
--   ```lean
--   theorem Logic.JFeature.pval_eq_one_of_floor{T : Ω → ℝ} (h : ∀ w, 1 ≤ T w) : pval T 1 = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/JFeatureMaxStatistic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/JFeatureMaxStatistic.lean#L84

-- Thm stub generated from Logic/JFeatureMaxStatistic.lean
import Mathlib
import Definitions.Def_Logic_JFeatureMaxStatistic
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

open Logic.JFeature

open Finset


variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

theorem Logic.JFeature.pval_eq_one_of_floor{T : Ω → ℝ} (h : ∀ w, 1 ≤ T w) : pval T 1 = 1 := by sorry
