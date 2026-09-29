-- Prove2me | Definitions.Def_Applications_JokeSurpriseUniqueness
-- name    : Applications_JokeSurpriseUniqueness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:26.977093+00:00
-- url     : https://prove2.me/theorems/99345678-1503-4f0c-8dc5-5881a258c037
-- title:
--   Aether Catalog definitions — Applications_JokeSurpriseUniqueness
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.JokeSurpriseUniqueness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/JokeSurpriseUniqueness.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_JokeSurpriseStability

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

namespace JokeSurpriseUniqueness

/-! ### A monotone Cauchy equation -/


/-! ### Humor scales -/

/-- A **humor scale**: an assignment of a surprise value to each pair of extreme
readings `m ≤ M`, which is blind to absolute position, additive under staged telling,
and monotone in the divergence of the readings. -/
structure HumorScale where
  /-- The surprise assigned to a setup whose extreme readings are `m` and `M`. -/
  toFun : ℝ → ℝ → ℝ
  /-- Position blindness: shifting all readings does not change the surprise. -/
  trans_inv : ∀ m M c : ℝ, m ≤ M → toFun (m + c) (M + c) = toFun m M
  /-- Staged telling: surprise accumulates along a decomposition of the reading gap. -/
  concat : ∀ a b c : ℝ, a ≤ b → b ≤ c → toFun a b + toFun b c = toFun a c
  /-- Monotonicity: a wider gap of readings is at least as surprising. -/
  mono : ∀ a b c : ℝ, a ≤ b → b ≤ c → toFun a b ≤ toFun a c

namespace HumorScale

variable (V : HumorScale)

/-- The **unit of a humor scale**: the surprise of the unit reading gap. -/
def scale : ℝ := V.toFun 0 1




/-- **The axioms are consistent.** The range functional is a humor scale, with unit
`1`. -/
def rangeScale : HumorScale where
  toFun := fun m M => M - m
  trans_inv := by intro m M c _; ring
  concat := by intro a b c _ _; ring
  mono := by intro a b c _ hbc; linarith





end HumorScale

end JokeSurpriseUniqueness


