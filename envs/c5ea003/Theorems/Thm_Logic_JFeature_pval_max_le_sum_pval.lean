-- Prove2me | Theorems.Thm_Logic_JFeature_pval_max_le_sum_pval
-- name    : Logic.JFeature.pval_max_le_sum_pval
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:29:18.721367+00:00
-- url     : https://prove2.me/theorems/540e48f8-2f35-47ec-82d0-1ccf5620f2bf
-- title:
--   Union bound over the scanned cells.
-- statement:
--   **Union bound over the scanned cells.**  The p-value of the max statistic is
--   at most the sum of the per-cell p-values — the exact content of the Bonferroni
--   correction, and the reason a per-cell `p = 0.36` says nothing about a scan.
--
--   ```lean
--   theorem Logic.JFeature.pval_max_le_sum_pval(T : κ → Ω → ℝ) (hκ : (univ : Finset κ).Nonempty) (t : ℝ) :
--       pval (maxStat T hκ) t ≤ ∑ c : κ, pval (T c) t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/JFeatureMaxStatistic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/JFeatureMaxStatistic.lean#L102

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









/-! ### Scanning many cells: union bound and Bonferroni -/

variable {κ : Type*} [Fintype κ]

theorem Logic.JFeature.pval_max_le_sum_pval(T : κ → Ω → ℝ) (hκ : (univ : Finset κ).Nonempty) (t : ℝ) :
    pval (maxStat T hκ) t ≤ ∑ c : κ, pval (T c) t := by sorry
