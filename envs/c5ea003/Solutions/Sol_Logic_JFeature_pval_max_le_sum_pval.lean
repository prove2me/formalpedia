-- Prove2me | solution 1 for Logic.JFeature.pval_max_le_sum_pval
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:13:35.875277+00:00
-- url     : https://prove2.me/submissions/8e39fa00-d320-4e2b-8d6d-376a8044da14

-- Sol generated from Logic/JFeatureMaxStatistic.lean
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




/-! ### Exact finite-sample validity of the permutation p-value -/





open Logic.JFeature in
theorem solution(T : κ → Ω → ℝ) (hκ : (univ : Finset κ).Nonempty) (t : ℝ) :
    pval (maxStat T hκ) t ≤ ∑ c : κ, pval (T c) t := by
  classical
  have hsub : univ.filter (fun w => t ≤ maxStat T hκ w)
      ⊆ (univ : Finset κ).biUnion (fun c => univ.filter (fun w => t ≤ T c w)) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, maxStat,
      Finset.le_sup'_iff] at hw
    obtain ⟨c, hc⟩ := hw
    exact Finset.mem_biUnion.2 ⟨c, Finset.mem_univ c, by simp [hc]⟩
  have hcard : ((univ.filter (fun w => t ≤ maxStat T hκ w)).card : ℝ)
      ≤ ∑ c : κ, ((univ.filter (fun w => t ≤ T c w)).card : ℝ) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := (univ : Finset κ))
      (t := fun c => univ.filter (fun w => t ≤ T c w))
    have : (univ.filter (fun w => t ≤ maxStat T hκ w)).card
        ≤ ∑ c : κ, (univ.filter (fun w => t ≤ T c w)).card := le_trans h1 h2
    exact_mod_cast this
  rw [pval]
  calc ((univ.filter (fun w => t ≤ maxStat T hκ w)).card : ℝ) / (Fintype.card Ω : ℝ)
      ≤ (∑ c : κ, ((univ.filter (fun w => t ≤ T c w)).card : ℝ)) / (Fintype.card Ω : ℝ) := by
        gcongr
    _ = ∑ c : κ, pval (T c) t := by
        rw [Finset.sum_div]; rfl
