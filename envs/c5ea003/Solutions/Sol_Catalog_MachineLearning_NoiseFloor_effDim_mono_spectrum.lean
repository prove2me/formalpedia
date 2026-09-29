-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.effDim_mono_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:39:13.406623+00:00
-- url     : https://prove2.me/submissions/82770ac6-69c5-4317-9426-b78bcdb403ea

-- Sol generated from MachineLearning/NoiseFloor/EffectiveDimension.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
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

omit [Fintype ι] in
lemma denom_pos (ha : ∀ i, 0 ≤ a i) (hb : 0 < b) (i : ι) : 0 < a i + b := by
  have := ha i; linarith













variable {a : ι → ℝ} {b : ℝ}





open Catalog.MachineLearning.NoiseFloor in
theorem solution{a a' : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : 0 < b)
    (h : ∀ i, a i ≤ a' i) : effDim a b ≤ effDim a' b := by
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : 0 < a i + b := denom_pos ha hb i
  have h2 : 0 < a' i + b := by have := (ha i).trans (h i); linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [ha i, h i]
