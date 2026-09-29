-- Prove2me | solution 1 for Logic.JFeature.perm_pval_valid
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:13:34.827976+00:00
-- url     : https://prove2.me/submissions/d0b73f95-c02b-4017-8351-1c5a13c05892

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



lemma card_pos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
  have : 0 < Fintype.card Ω := Fintype.card_pos
  exact_mod_cast this






/-! ### Scanning many cells: union bound and Bonferroni -/

variable {κ : Type*} [Fintype κ]




/-! ### Exact finite-sample validity of the permutation p-value -/





open Logic.JFeature in
theorem solution(T : Ω → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    (((univ.filter (fun w => pval T (T w) ≤ α)).card : ℝ)) ≤ α * (Fintype.card Ω : ℝ) := by
  classical
  set S := univ.filter (fun w => pval T (T w) ≤ α) with hS
  rcases S.eq_empty_or_nonempty with hemp | hne
  · rw [hemp]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · obtain ⟨w₀, hw₀S, hw₀min⟩ := S.exists_min_image T hne
    have hw₀ : pval T (T w₀) ≤ α := by
      have := Finset.mem_filter.1 (hS ▸ hw₀S)
      exact this.2
    have hsub : S ⊆ univ.filter (fun w => T w₀ ≤ T w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hw₀min w hw
    have hcard : ((S.card : ℝ)) ≤ ((univ.filter (fun w => T w₀ ≤ T w)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hpv : ((univ.filter (fun w => T w₀ ≤ T w)).card : ℝ)
        = pval T (T w₀) * (Fintype.card Ω : ℝ) := by
      rw [pval, div_mul_cancel₀]
      exact ne_of_gt card_pos
    rw [hpv] at hcard
    have := mul_le_mul_of_nonneg_right hw₀ (le_of_lt (card_pos (Ω := Ω)))
    linarith
