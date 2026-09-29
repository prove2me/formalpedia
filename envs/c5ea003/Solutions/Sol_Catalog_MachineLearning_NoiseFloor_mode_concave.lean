-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.mode_concave
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:37:57.655891+00:00
-- url     : https://prove2.me/submissions/64df57d8-7689-4d4a-b7fa-e3bed2104bff

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














variable {a : ι → ℝ} {b : ℝ}





open Catalog.MachineLearning.NoiseFloor in
theorem solution{x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hb : 0 < b) {w : ℝ}
    (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
    w * (x / (x + b)) + (1 - w) * (y / (y + b))
      ≤ (w * x + (1 - w) * y) / ((w * x + (1 - w) * y) + b) := by
  have hX : 0 < x + b := by linarith
  have hY : 0 < y + b := by linarith
  have h1w : (0 : ℝ) ≤ 1 - w := by linarith
  have hZ : 0 < w * x + (1 - w) * y + b := by
    have := mul_nonneg hw₀ hx
    have := mul_nonneg h1w hy
    linarith
  have lhs_eq : w * (x / (x + b)) + (1 - w) * (y / (y + b))
      = (w * x * (y + b) + (1 - w) * y * (x + b)) / ((x + b) * (y + b)) := by
    field_simp
  rw [lhs_eq, div_le_div_iff₀ (by positivity) hZ]
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hb.le hw₀) h1w) (sq_nonneg (x - y))]
