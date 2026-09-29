-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.effDim_concave
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:39:11.679228+00:00
-- url     : https://prove2.me/submissions/54b94d86-b3c2-46c0-92f0-5c2848d8ac70

-- Sol generated from MachineLearning/NoiseFloor/EffectiveDimension.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Theorems.Thm_Catalog_MachineLearning_NoiseFloor_mode_concave
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





open Catalog.MachineLearning.NoiseFloor in
theorem solution{a a' : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (ha' : ∀ i, 0 ≤ a' i)
    (hb : 0 < b) {w : ℝ} (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
    w * effDim a b + (1 - w) * effDim a' b
      ≤ effDim (fun i => w * a i + (1 - w) * a' i) b := by
  rw [effDim, effDim, effDim, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => mode_concave (ha i) (ha' i) hb hw₀ hw₁
