-- Prove2me | Definitions.Def_P2MAssembly_Chapter25
-- name    : P2MAssembly_Chapter25
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T16:34:32.948301+00:00
-- url     : https://prove2.me/theorems/44d1ff30-060a-48e2-bf05-fb5818b21f37
-- title:
--   The needle projection, crossing indicator, and parameter rectangle
-- statement:
--   For real parameters l,x,theta, define the horizontal projection interval
--   $$J_l(x,\theta)=[x-l\sin\theta/2,\ x+l\sin\theta/2].$$
--   Its crossing indicator is 1 when 0 belongs to this interval and 0 otherwise. For any map $B:\Omega\to\mathbb R^2$, the function $N_l$ is the composition of this indicator with B. The parameter rectangle for spacing d is $[-d/2,d/2]\times[0,\pi]$; theta represents angle from the vertical axis.
--
--   The definitions themselves impose no positivity, measurability, or uniform-distribution condition. Those assumptions appear in the subsequent integral and probability theorems. Closed intervals with their lower endpoint above their upper endpoint are empty. These definitions are retained from Mathlib Archive.
-- source:
--   Mathlib Archive definitions, Enrico Z. Borba, Apache 2.0: https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Archive/Wiedijk100Theorems/BuffonsNeedle.lean#L99. The generated bundle retains the upstream author and license header; these definitions are not attributed to the importing repository.

import Init
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Density
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Notation
import Mathlib

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

/--
Projection of a needle onto the x-axis. The needle's center is at x-coordinate `x`, of length
`l` and angle `θ`. Note, `θ` is measured relative to the y-axis, that is, a vertical needle has
`θ = 0`.
-/
def needleProjX (x θ : ℝ) : Set ℝ := Set.Icc (x - θ.sin * l / 2) (x + θ.sin * l / 2)

/--
The indicator function of whether a needle at position `⟨x, θ⟩ : ℝ × ℝ` crosses the line `x = 0`.

In order to faithfully model the problem, we compose `needleCrossesIndicator` with a random
variable `B : Ω → ℝ × ℝ` with uniform distribution on `[-d/2, d/2] × [0, π]`. Then, by symmetry,
the probability that the needle crosses `x = 0`, is the same as the probability of a needle
crossing any of the infinitely spaced vertical lines distance `d` apart.
-/
noncomputable def needleCrossesIndicator (p : ℝ × ℝ) : ℝ :=
  Set.indicator (needleProjX l p.1 p.2) 1 0

/--
A random variable representing whether the needle crosses a line.

The line is at `x = 0`, and therefore a needle crosses the line if its projection onto the x-axis
contains `0`. This random variable is `1` if the needle crosses the line, and `0` otherwise.
-/
noncomputable def N : Ω → ℝ := needleCrossesIndicator l ∘ B

/--
The possible x-positions and angle relative to the y-axis of a needle.
-/
abbrev needleSpace : Set (ℝ × ℝ) := Set.Icc (-d / 2) (d / 2) ×ˢ Set.Icc 0 π

























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


