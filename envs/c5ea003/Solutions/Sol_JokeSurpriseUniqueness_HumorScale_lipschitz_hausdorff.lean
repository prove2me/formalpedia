-- Prove2me | solution 1 for JokeSurpriseUniqueness.HumorScale.lipschitz_hausdorff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T21:56:21.544594+00:00
-- url     : https://prove2.me/submissions/ded3848c-134e-4870-b0a6-910fbe7062ed

-- Sol generated from Applications/JokeSurpriseUniqueness.lean
import Mathlib
import Definitions.Def_Applications_JokeSurpriseAlgebra
import Definitions.Def_Applications_JokeSurpriseStability
import Definitions.Def_Applications_JokeSurpriseUniqueness
import Theorems.Thm_JokeSurpriseStability_abs_diam_sub_diam_le_two_hausdorffDist
import Theorems.Thm_JokeSurpriseStability_humor_eq_diam
import Theorems.Thm_JokeSurpriseUniqueness_HumorScale_eq_scale_mul

/-!
# Why *this* invariant? A uniqueness theorem for surprise

The two preceding files of this thread take the formula `humor S = max' S - min' S`
(equivalently `Metric.diam S`, by `JokeSurpriseStability.humor_eq_diam`) as given, and
study its algebra (`Applications.JokeSurpriseAlgebra`,
`Applications.JokeColimitUniversality`) and its stability
(`Applications.JokeSurpriseStability`). The obvious objection is that the formula is
*chosen*: any monotone functional on setups would produce a plausible-looking theory.

This file removes the choice. We axiomatise what a *humor scale* must satisfy —

* **position blindness**: a joke is not funnier for being told about larger numbers
  (translation invariance);
* **staged telling**: telling a joke in two consecutive stages accumulates the surprise
  of the stages (concatenation additivity);
* **monotonicity**: widening the gap between the extreme readings cannot reduce
  surprise —

and prove that these three axioms pin the invariant down **completely**:

* `HumorScale.eq_scale_mul` : every humor scale is `V m M = c · (M - m)` with
  `c = V 0 1`;
* `HumorScale.scale_nonneg` : the constant is nonnegative;
* `HumorScale.eq_scale_mul_humor` : on setups, every humor scale is a nonnegative
  multiple of the catalog's `humor`;
* `HumorScale.ext_of_scale_eq` : a humor scale is determined by its value on the unit
  gap — the theory has exactly one degree of freedom, the choice of unit.

Consequently every theorem of the thread transfers automatically to *any* admissible
invariant, without re-proof:

* `HumorScale.submodular` : every humor scale is submodular;
* `HumorScale.lipschitz_hausdorff` : every humor scale is `2c`-Lipschitz for the
  Hausdorff distance between setups.

The technical heart is `cauchy_of_monotone`: a monotone solution of the Cauchy
functional equation on `[0, ∞)` is linear. It is proved from scratch (rational
dilations `g (k s) = k g s`, the floor sandwich `k/n ≤ t ≤ (k+1)/n`, and an
Archimedean limit), since a monotone — as opposed to continuous or measurable —
Cauchy theorem is not available off the shelf.

-- !-- Lab Notes -- !--
Hypothesis (H7): the range/diameter formula is not a modelling choice but is *forced*
by position blindness, staged telling, and monotonicity.
Hypothesis (H8): if H7 holds, the whole thread (submodularity, Hausdorff stability) is
axiom-independent and transfers to every admissible invariant.

Experiment: H7 was reduced to a Cauchy functional equation for `g t = V 0 t` on
`[0, ∞)`. The additivity `g (s + t) = g s + g t` comes from concatenation plus
translation invariance; monotonicity of `g` from the third axiom. The linearity
`g t = g 1 · t` was then proved by hand: `g (k s) = k g s` by induction, hence
`g (1/n) = g 1 / n` and `g (k/n) = g 1 · k / n`; sandwiching `t` between
`⌊n t⌋/n` and `(⌊n t⌋ + 1)/n` gives `|g t - g 1 · t| ≤ g 1 / n` for every `n`, and the
Archimedean property finishes. Non-vacuity was checked by exhibiting the range scale
`rangeScale` (with `c = 1`) as a model of the axioms.

Analysis: H7 and H8 both survive, and they retro-justify the earlier files: every
theorem previously proved about `humor` is a theorem about *any* invariant obeying the
three axioms, up to the scale factor `c`.

Critique: monotonicity is essential and not decorative — without it, a Hamel-basis
solution of the Cauchy equation gives a wildly discontinuous "humor scale" that is
translation invariant and concatenation additive but not proportional to the range.
The axioms are consistent (`rangeScale`) and, by `ext_of_scale_eq`, categorical up to
the single scale parameter.

Synthesis: surprise is the unique — up to choice of unit — position-blind, stage-
additive, monotone measure of a setup; the range formula of the catalog is its
normalisation at `c = 1`.
-/

open Finset Metric JokeSurpriseAlgebra JokeSurpriseStability

open JokeSurpriseUniqueness

/-! ### A monotone Cauchy equation -/


/-! ### Humor scales -/


open HumorScale

variable (V : HumorScale)


/-- The **unit is nonnegative**. -/
theorem scale_nonneg : 0 ≤ V.scale := by
  have h0 : V.toFun 0 0 + V.toFun 0 0 = V.toFun 0 0 := V.concat 0 0 0 le_rfl le_rfl
  have h1 : V.toFun 0 0 ≤ V.toFun 0 1 := V.mono 0 0 1 le_rfl (by norm_num)
  simp only [scale]
  linarith





/-- **On setups, every humor scale is a multiple of the catalog's `humor`.** -/
theorem eq_scale_mul_humor (S : Finset ℝ) (hS : S.Nonempty) :
    V.toFun (S.min' hS) (S.max' hS) = V.scale * humor S hS := by
  rw [V.eq_scale_mul _ _ (S.min'_le_max' hS)]
  rfl





open JokeSurpriseUniqueness.HumorScale
open JokeSurpriseUniqueness.HumorScale
namespace JokeSurpriseUniqueness.HumorScale
/-- **On setups, every humor scale is a multiple of the catalog's `humor`.** -/
theorem eq_scale_mul_humor (S : Finset ℝ) (hS : S.Nonempty) :
    V.toFun (S.min' hS) (S.max' hS) = V.scale * humor S hS := by
  rw [V.eq_scale_mul _ _ (S.min'_le_max' hS)]
  rfl

end JokeSurpriseUniqueness.HumorScale

namespace JokeSurpriseUniqueness.HumorScale
/-- The **unit is nonnegative**. -/
theorem scale_nonneg : 0 ≤ V.scale := by
  have h0 : V.toFun 0 0 + V.toFun 0 0 = V.toFun 0 0 := V.concat 0 0 0 le_rfl le_rfl
  have h1 : V.toFun 0 0 ≤ V.toFun 0 1 := V.mono 0 0 1 le_rfl (by norm_num)
  simp only [scale]
  linarith

end JokeSurpriseUniqueness.HumorScale

open JokeSurpriseUniqueness in
theorem solution(S T : Finset ℝ) (hS : S.Nonempty) (hT : T.Nonempty) :
    |V.toFun (S.min' hS) (S.max' hS) - V.toFun (T.min' hT) (T.max' hT)|
      ≤ 2 * V.scale * hausdorffDist (S : Set ℝ) (T : Set ℝ) := by
  have hbS : Bornology.IsBounded (S : Set ℝ) := S.finite_toSet.isBounded
  have hbT : Bornology.IsBounded (T : Set ℝ) := T.finite_toSet.isBounded
  have hne : hausdorffEDist (S : Set ℝ) (T : Set ℝ) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (by exact_mod_cast hS)
      (by exact_mod_cast hT) hbS hbT
  have hmetric := abs_diam_sub_diam_le_two_hausdorffDist hbS hbT hne
  rw [← humor_eq_diam S hS, ← humor_eq_diam T hT] at hmetric
  rw [V.eq_scale_mul_humor _ hS, V.eq_scale_mul_humor _ hT, ← mul_sub, abs_mul,
    abs_of_nonneg V.scale_nonneg]
  calc V.scale * |humor S hS - humor T hT|
      ≤ V.scale * (2 * hausdorffDist (S : Set ℝ) (T : Set ℝ)) :=
        mul_le_mul_of_nonneg_left hmetric V.scale_nonneg
    _ = 2 * V.scale * hausdorffDist (S : Set ℝ) (T : Set ℝ) := by ring
