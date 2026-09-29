-- Prove2me | solution 1 for JokeSurpriseUniqueness.HumorScale.eq_scale_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:40:45.736144+00:00
-- url     : https://prove2.me/submissions/54d4aaf4-7cca-4e43-b653-eedf7c1240b9

-- Sol generated from Applications/JokeSurpriseUniqueness.lean
import Mathlib
import Definitions.Def_Applications_JokeSurpriseStability
import Definitions.Def_Applications_JokeSurpriseUniqueness
import Theorems.Thm_JokeSurpriseUniqueness_cauchy_of_monotone

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












open JokeSurpriseUniqueness.HumorScale in
theorem solution(m M : ℝ) (h : m ≤ M) : V.toFun m M = V.scale * (M - m) := by
  set g : ℝ → ℝ := fun t => V.toFun 0 t with hg
  have hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → g (s + t) = g s + g t := by
    intro s t hs ht
    have h1 : V.toFun 0 s + V.toFun s (s + t) = V.toFun 0 (s + t) :=
      V.concat 0 s (s + t) hs (by linarith)
    have h2 : V.toFun (0 + s) (t + s) = V.toFun 0 t := V.trans_inv 0 t s ht
    rw [zero_add] at h2
    have h3 : t + s = s + t := by ring
    rw [h3] at h2
    simp only [hg]
    linarith
  have hmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → g s ≤ g t := fun s t hs hst =>
    V.mono 0 s t hs hst
  have hlin := cauchy_of_monotone g hadd hmono (M - m) (by linarith)
  have hshift : V.toFun (0 + m) ((M - m) + m) = V.toFun 0 (M - m) :=
    V.trans_inv 0 (M - m) m (by linarith)
  rw [zero_add] at hshift
  have hMm : M - m + m = M := by ring
  rw [hMm] at hshift
  rw [hshift]
  simpa [hg, scale] using hlin
