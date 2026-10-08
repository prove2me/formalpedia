-- Prove2me | solution 1 for ProofsInTheBook.Chapter25.chapter25_measure_theoretic_short
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:44:53.12309+00:00
-- url     : https://prove2.me/submissions/ea1928c3-f0e7-4e6c-aa6d-34f725f39826

import Init
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Density
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Notation
import Mathlib
import Definitions.Def_P2MAssembly_Chapter25


/- Original source header (imports hoisted):
/-
Copyright (c) 2024 Enrico Z. Borba. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enrico Z. Borba
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Density
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Notation
-/
/- Source module: Archive.Wiedijk100Theorems.BuffonsNeedle -/
section


/-!

# Freek № 99: Buffon's Needle

This file proves Theorem 99 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/), also
known as Buffon's Needle, which gives the probability of a needle of length `l > 0` crossing any
one of infinite vertical lines spaced out `d > 0` apart.

The two cases are proven in `buffon_short` and `buffon_long`.

## Overview of the Proof

We define a random variable `B : Ω → ℝ × ℝ` with a uniform distribution on `[-d/2, d/2] × [0, π]`.
This represents the needle's x-position and angle with respect to a vertical line. By symmetry, we
need to consider only a single vertical line positioned at `x = 0`. A needle therefore crosses the
vertical line if its projection onto the x-axis contains `0`.

We define a random variable `N : Ω → ℝ` that is `1` if the needle crosses a vertical line, and `0`
otherwise. This is defined as `fun ω => Set.indicator (needleProjX l (B ω).1 (B ω).2) 1 0`.
f
As in many references, the problem is split into two cases, `l ≤ d` (`buffon_short`), and `d ≤ l`
(`buffon_long`). For both cases, we show that
```lean
ℙ[N] = (d * π) ⁻¹ *
    ∫ θ in 0..π,
      ∫ x in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1
```
In the short case `l ≤ d`, we show that `[-l * θ.sin/2, l * θ.sin/2] ⊆ [-d/2, d/2]`
(`short_needle_inter_eq`), and therefore the inner integral simplifies to
```lean
∫ x in (-θ.sin * l / 2)..(θ.sin * l / 2), 1 = θ.sin * l
```
Which then concludes in the short case being `ℙ[N] = (2 * l) / (d * π)`.

In the long case, `l ≤ d` (`buffon_long`), we show the outer integral simplifies to
```lean
∫ θ in 0..π, min d (θ.sin * l)
```
which can be expanded to
```lean
2 * (
  ∫ θ in 0..(d / l).arcsin, min d (θ.sin * l) +
  ∫ θ in (d / l).arcsin..(π / 2), min d (θ.sin * l)
)
```
We then show the two integrals equal their respective values `l - √(l^2 - d^2)` and
`(π / 2 - (d / l).arcsin) * d`. Then with some algebra we conclude
```lean
ℙ[N] = (2 * l) / (d * π) - 2 / (d * π) * (√(l^2 - d^2) + d * (d / l).arcsin) + 1
```

## References

* https://en.wikipedia.org/wiki/Buffon%27s_needle_problem
* https://www.math.leidenuniv.nl/~hfinkeln/seminarium/stelling_van_Buffon.pdf
* https://www.isa-afp.org/entries/Buffons_Needle.html

-/

open MeasureTheory (MeasureSpace IsProbabilityMeasure Measure pdf.IsUniform)
open ProbabilityTheory Real

namespace BuffonsNeedle

variable
  /- Probability theory variables. -/
  {Ω : Type*} [MeasureSpace Ω]
  /- Buffon's needle variables. -/
  /-
    - `d > 0` is the distance between parallel lines.
    - `l > 0` is the length of the needle.
  -/
  (d l : ℝ)
  (hd : 0 < d)
  (hl : 0 < l)
  /- `B = (X, Θ)` is the joint random variable for the x-position and angle of the needle. -/
  (B : Ω → ℝ × ℝ)
  (hBₘ : Measurable B)
  /- `B` is uniformly distributed on `[-d/2, d/2] × [0, π]`. -/
  (hB : pdf.IsUniform B ((Set.Icc (-d / 2) (d / 2)) ×ˢ (Set.Icc 0 π)) ℙ)









include hd in
lemma volume_needleSpace : ℙ (needleSpace d) = ENNReal.ofReal (d * π) := by
  simp_rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, Real.volume_Icc,
    ENNReal.ofReal_mul hd.le]
  ring_nf

lemma measurable_needleCrossesIndicator : Measurable (needleCrossesIndicator l) := by
  unfold needleCrossesIndicator
  refine Measurable.indicator measurable_const (IsClosed.measurableSet (IsClosed.and ?_ ?_)) <;>
    simp only [tsub_le_iff_right, zero_add, ← neg_le_iff_add_nonneg']
  · exact isClosed_le continuous_fst (by fun_prop)
  · exact isClosed_le continuous_fst.neg (by fun_prop)

lemma stronglyMeasurable_needleCrossesIndicator :
    MeasureTheory.StronglyMeasurable (needleCrossesIndicator l) := by
  refine stronglyMeasurable_iff_measurable_separable.mpr
    ⟨measurable_needleCrossesIndicator l, {0, 1}, ?separable⟩
  have range_finite : Set.Finite ({0, 1} : Set ℝ) := by
    simp only [Set.finite_singleton, Set.Finite.insert]
  refine ⟨range_finite.countable, ?subset_closure⟩
  rw [IsClosed.closure_eq range_finite.isClosed, Set.subset_def, Set.range]
  intro x ⟨p, hxp⟩
  by_cases hp : 0 ∈ needleProjX l p.1 p.2
  · simp_rw [needleCrossesIndicator, Set.indicator_of_mem hp, Pi.one_apply] at hxp
    apply Or.inr hxp.symm
  · simp_rw [needleCrossesIndicator, Set.indicator_of_notMem hp] at hxp
    apply Or.inl hxp.symm

include hd in
lemma integrable_needleCrossesIndicator :
    MeasureTheory.Integrable (needleCrossesIndicator l)
      (Measure.prod
        (Measure.restrict ℙ (Set.Icc (-d / 2) (d / 2)))
        (Measure.restrict ℙ (Set.Icc 0 π))) := by
  have needleCrossesIndicator_nonneg p : 0 ≤ needleCrossesIndicator l p := by
    apply Set.indicator_apply_nonneg
    simp only [Pi.one_apply, zero_le_one, implies_true]
  have needleCrossesIndicator_le_one p : needleCrossesIndicator l p ≤ 1 := by
    unfold needleCrossesIndicator
    by_cases hp : 0 ∈ needleProjX l p.1 p.2
    · simp_rw [Set.indicator_of_mem hp, Pi.one_apply, le_refl]
    · simp_rw [Set.indicator_of_notMem hp, zero_le_one]
  refine And.intro
    (stronglyMeasurable_needleCrossesIndicator l).aestronglyMeasurable
    ((MeasureTheory.hasFiniteIntegral_iff_norm (needleCrossesIndicator l)).mpr ?_)
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono (g := 1) ?le_const) ?lt_top
  case le_const =>
    intro p
    simp only [Real.norm_eq_abs, abs_of_nonneg (needleCrossesIndicator_nonneg _),
      ENNReal.ofReal_le_one, Pi.one_apply]
    exact needleCrossesIndicator_le_one p
  case lt_top =>
    simp_rw [Pi.one_apply, MeasureTheory.lintegral_const, one_mul, Measure.prod_restrict,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Measure.prod_prod, Real.volume_Icc,
      neg_div, sub_neg_eq_add, add_halves, sub_zero, ← ENNReal.ofReal_mul hd.le,
      ENNReal.ofReal_lt_top]

include hd hB hBₘ in
/--
This is a common step in both the short and the long case to simplify the expectation of the
needle crossing a line to a double integral.
```lean
∫ (θ : ℝ) in Set.Icc 0 π,
  ∫ (x : ℝ) in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1
```
The domain of the inner integral is simpler in the short case, where the intersection is
equal to `Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2)` by `short_needle_inter_eq`.
-/
lemma buffon_integral :
    𝔼[N l B] = (d * π)⁻¹ *
      ∫ (θ : ℝ) in Set.Icc 0 π,
      ∫ (_ : ℝ) in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1 := by
  simp_rw [N, Function.comp_apply]
  rw [
    ← MeasureTheory.integral_map hBₘ.aemeasurable
      (stronglyMeasurable_needleCrossesIndicator l).aestronglyMeasurable,
    hB, ProbabilityTheory.cond, MeasureTheory.integral_smul_measure, volume_needleSpace d hd,
    ← ENNReal.ofReal_inv_of_pos (mul_pos hd Real.pi_pos),
    ENNReal.toReal_ofReal (inv_nonneg.mpr (mul_nonneg hd.le Real.pi_pos.le)), smul_eq_mul,
  ]
  refine mul_eq_mul_left_iff.mpr (Or.inl ?_)
  have : MeasureTheory.IntegrableOn (needleCrossesIndicator l)
      (Set.Icc (-d / 2) (d / 2) ×ˢ Set.Icc 0 π) := by
    simp_rw [MeasureTheory.IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict,
      integrable_needleCrossesIndicator d l hd]
  rw [Measure.volume_eq_prod, MeasureTheory.setIntegral_prod _ this,
    MeasureTheory.integral_integral_swap ?integrable]
  case integrable => simp_rw [Function.uncurry_def, Prod.mk.eta,
    integrable_needleCrossesIndicator d l hd]
  simp only [needleCrossesIndicator, needleProjX]
  have indicator_eq (x θ : ℝ) :
      Set.indicator (Set.Icc (x - θ.sin * l / 2) (x + θ.sin * l / 2)) 1 0 =
      Set.indicator (Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2)) (1 : ℝ → ℝ) x := by
    simp_rw [Set.indicator, Pi.one_apply, Set.mem_Icc, tsub_le_iff_right, zero_add, neg_mul]
    have :
        x ≤ Real.sin θ * l / 2 ∧ 0 ≤ x + Real.sin θ * l / 2 ↔
        -(Real.sin θ * l) / 2 ≤ x ∧ x ≤ Real.sin θ * l / 2 := by
      rw [neg_div, and_comm, ← tsub_le_iff_right, zero_sub]
    by_cases h : x ≤ Real.sin θ * l / 2 ∧ 0 ≤ x + Real.sin θ * l / 2
    · rw [if_pos h, if_pos (this.mp h)]
    · rw [if_neg h, if_neg (this.not.mp h)]
  simp_rw [indicator_eq, MeasureTheory.setIntegral_indicator measurableSet_Icc, Pi.one_apply]

include hl in
/--
From `buffon_integral`, in both the short and the long case, we have
```lean
𝔼[N l B] = (d * π)⁻¹ *
  ∫ (θ : ℝ) in Set.Icc 0 π,
    ∫ (x : ℝ) in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1
```
With this lemma, in the short case, the inner integral's domain simplifies to
`Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2)`.
-/
lemma short_needle_inter_eq (h : l ≤ d) (θ : ℝ) :
    Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2) =
    Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2) := by
  rw [Set.Icc_inter_Icc, max_div_div_right zero_le_two,
    min_div_div_right zero_le_two, neg_mul, max_neg_neg, mul_comm,
    min_eq_right ((mul_le_of_le_one_right hl.le θ.sin_le_one).trans h)]

include hd hBₘ hB hl in
/--
Buffon's Needle, the short case (`l ≤ d`). The probability of the needle crossing a line
equals `(2 * l) / (d * π)`.
-/
theorem buffon_short (h : l ≤ d) : ℙ[N l B] = (2 * l) * (d * π)⁻¹ := by
  simp_rw [buffon_integral d l hd B hBₘ hB, short_needle_inter_eq d l hl h _,
    MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
    Real.volume_Icc, smul_eq_mul, mul_one, mul_comm (d * π)⁻¹ _,
    mul_eq_mul_right_iff]
  apply Or.inl
  ring_nf
  have : ∀ᵐ θ, θ ∈ Set.Icc 0 π → ENNReal.toReal (ENNReal.ofReal (θ.sin * l)) = θ.sin * l := by
    have (θ : ℝ) (hθ : θ ∈ Set.Icc 0 π) : 0 ≤ θ.sin * l :=
      mul_nonneg (Real.sin_nonneg_of_mem_Icc hθ) hl.le
    simp_rw [ENNReal.toReal_ofReal_eq_iff, MeasureTheory.ae_of_all _ this]
  simp_rw [MeasureTheory.setIntegral_congr_ae measurableSet_Icc this,
    ← smul_eq_mul, integral_smul_const, smul_eq_mul, mul_comm, mul_eq_mul_left_iff,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_sin, Real.cos_zero, Real.cos_pi, sub_neg_eq_add, one_add_one_eq_two, true_or]











end BuffonsNeedle

end

/- Original source header (imports hoisted):
import Mathlib
import Archive.Wiedijk100Theorems.BuffonsNeedle
-/
/- Source module: ProofsInTheBook.Chapter25 -/
section


/-!
# Chapter 25: Buffon's needle problem

From "Proofs from THE BOOK":

**Buffon's needle**: A needle of length ℓ dropped on parallel lines
spaced d apart (ℓ ≤ d) crosses a line with probability 2ℓ/(πd).

The book's proof uses the linearity of expectation: any curve of
length L crosses E[crossings] = 2L/(πd) lines, proved by decomposing
into infinitesimal segments and using rotational symmetry.

Formalization status: this file now removes the previous escape hatch where a
structure field asserted the expected-value identity.  The public `chapter25`
states the short-needle theorem as an explicit density-level probability
calculation: the center distance from the nearest line is averaged uniformly on
`[0,d/2]`, the angle is averaged uniformly on `[0,π]`, and the resulting
one-dimensional angle integral is evaluated.

Remaining gap to the full measure-theoretic book statement: replace the
density-level average with an actual product probability measure on
`[0,d/2] × [0,π]`, prove measurability of the crossing event, identify the
event integral with the conditional center-distance average used here, and
then derive the expectation/probability equality from the Bernoulli crossing
count.  No field below assumes this identity.
-/

namespace ProofsInTheBook.Chapter25

open scoped BigOperators























































/-!
### Faithful measure-theoretic statement

The density-level `chapter25` above evaluates an explicit angle integral but does
not carry an actual probability measure.  The genuine measure-theoretic Buffon
statement — the expectation `ℙ[N]` of the crossing indicator `N`, where the
needle's joint (center-position, angle) variable `B` is uniformly distributed on
`[-d/2, d/2] × [0, π]` — is provided by Mathlib's Archive proof of the Wiedijk
100-theorems entry `BuffonsNeedle`.  We expose both cases here so that Chapter 25
records the full probability statement, not just the density average.
-/





end ProofsInTheBook.Chapter25

end


open ProofsInTheBook.Chapter25
open scoped BigOperators
open MeasureTheory ProbabilityTheory Real

theorem solution {Ω : Type*} [MeasureSpace Ω]
    (d l : ℝ) (hd : 0 < d) (hl : 0 < l)
    (B : Ω → ℝ × ℝ) (hBₘ : Measurable B)
    (hB : MeasureTheory.pdf.IsUniform B
      ((Set.Icc (-d / 2) (d / 2)) ×ˢ (Set.Icc 0 π)) ℙ)
    (h : l ≤ d) :
    ℙ[BuffonsNeedle.N l B] = (2 * l) * (d * π)⁻¹ :=
  BuffonsNeedle.buffon_short d l hd hl B hBₘ hB h
