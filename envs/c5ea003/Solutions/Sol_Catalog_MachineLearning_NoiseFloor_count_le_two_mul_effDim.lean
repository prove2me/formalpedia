-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.count_le_two_mul_effDim
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:37:56.867804+00:00
-- url     : https://prove2.me/submissions/6753a61f-f1f7-4de1-be13-6f07a7b96eea

-- Sol generated from MachineLearning/NoiseFloor/EffectiveDimension.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Theorems.Thm_Catalog_MachineLearning_NoiseFloor_mode_mem_Ico
/-
# The Noise-Floor Principle, Part I: Effective Dimension

Round-6 hypothesis closure, Phase A.  This file develops the *spectral effective
dimension*

  `effDim a b = ∑ i, a i / (a i + b)`

of a nonnegative "signal spectrum" `a : ι → ℝ` measured at a "noise level" `b > 0`.
It is the scalar shadow of the matrix quantity `tr (A (A + b•1)⁻¹)` (the
*trace lemma frontier*, formalised in `TraceLemma.lean`), and it is the exact
value of the information-theoretic noise floor of any linear spectral filter
(formalised in `NoiseFloorPrinciple.lean`).

Main results:

* `effDim_nonneg`, `effDim_le_card`, `effDim_le_min`
* `effDim_le_trace_div`      — the *trace bound* `d_eff ≤ tr(a)/b`
* `effDim_antitone_level`    — monotone decreasing in the noise level
* `effDim_mono_spectrum`     — monotone increasing in the spectrum
* `effDim_doubling`          — `d_eff(b/2) ≤ 2 d_eff(b)`: the noise floor has no
                               sharp cliff (a Muckenhoupt-style doubling property)
* `effDim_scale_invariant`   — joint scaling invariance `d_eff(ca, cb) = d_eff(a,b)`
* `effDim_concave`           — concavity in the spectrum (mixing signals cannot help)
* `count_le_two_mul_effDim`  — `#{i : b ≤ a i} ≤ 2 d_eff`: every *resolvable* mode
                               contributes at least one half to the effective dimension.
-/

open Catalog.MachineLearning.NoiseFloor

open Finset

variable {ι : Type*} [Fintype ι]



variable {a : ι → ℝ} {b : ℝ}














variable {a : ι → ℝ} {b : ℝ}

omit [Fintype ι] in
/-- A mode whose power exceeds the noise level contributes at least `1/2`. -/
lemma half_le_mode (hb : 0 < b) {i : ι} (hi : b ≤ a i) : (1 : ℝ) / 2 ≤ a i / (a i + b) := by
  have hd : 0 < a i + b := by linarith
  rw [div_le_div_iff₀ (by norm_num) hd]
  linarith




open Catalog.MachineLearning.NoiseFloor in
theorem solution[DecidableEq ι] (ha : ∀ i, 0 ≤ a i) (hb : 0 < b) :
    ((univ.filter fun i => b ≤ a i).card : ℝ) ≤ 2 * effDim a b := by
  classical
  have h1 : ((univ.filter fun i => b ≤ a i).card : ℝ) * (2 : ℝ)⁻¹
      ≤ ∑ i ∈ univ.filter fun i => b ≤ a i, a i / (a i + b) := by
    have := Finset.card_nsmul_le_sum (univ.filter fun i => b ≤ a i)
      (fun i => a i / (a i + b)) ((1 : ℝ) / 2) (fun i hi => half_le_mode hb (mem_filter.1 hi).2)
    simpa [nsmul_eq_mul] using this
  have h2 : ∑ i ∈ univ.filter fun i => b ≤ a i, a i / (a i + b) ≤ effDim a b := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro i _ _
    exact (mode_mem_Ico ha hb i).1
  linarith
