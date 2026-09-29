-- Prove2me | solution 1 for FanoStrongBlocking.Pts_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:17:39.25686+00:00
-- url     : https://prove2.me/submissions/564084e5-2414-4653-88c5-092c5c9dd7ac

-- Sol generated from Geometry/FanoStrongBlocking/Core.lean
import Mathlib
import Definitions.Def_Geometry_FanoStrongBlocking_Core
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Fano-plane threshold for strong blocking sets (the `h = 1` case)

This file proves the `h = 1` specialization of the additive strong-blocking-set
problem: in the Fano plane `PG(2,2)` a finite set of points is a **strong blocking
set** (a *cutting blocking set*: it meets every line in a spanning subset) **iff it
contains at least `6` of the `7` points**.

## Model

We represent `PG(2,2)` by the nonzero vectors of `V = (ZMod 2)^3`.  Over `ZMod 2`
the only nonzero scalar is `1`, so the `7` projective points are exactly the `7`
nonzero vectors.  Three distinct nonzero points `a, b, c` are **collinear** iff
`a + b + c = 0` (equivalently `c = a + b`); each of the `7` lines has `3` points.

A line of `PG(2,2)` has `3` points, and a 3-point projective line is *spanned* by a
subset iff that subset has at least `2` points.  Hence a strong blocking set is a
set `S` meeting every line in `≥ 2` points, which we phrase as: for every line
`{a,b,c}`, at least two of `a, b, c` lie in `S`.

## Main result

`fano_strongBlocking_iff_six` : for `S ⊆ Pts`,
`StrongBlocking S ↔ 6 ≤ S.card`.

The crux is the structural lemma `card_le_five_of_two_missing` / `two_missing`:
two distinct missing points `p, q` create the "starved" line `{p, q, p+q}` that
contains at most one point of `S`.  This replaces a brute-force enumeration with a
genuine incidence argument.

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer): the strong-blocking threshold in `PG(2,2)` should be
  the codimension bound `3(q+1) - 1 = 6` specialized to `q = 2`; equivalently every
  minimal binary `[n,3]` code that is *minimal* (every codeword minimal) has
  `n ≥ 6`, with equality attained.  Bold form: the threshold is sharp at `6`, never
  `5`.
* Experiment (Experimenter): modelled points as nonzero vectors of `(ZMod 2)^3`,
  lines as zero-sum triples.  Proved the "unique third point" lemma `isLine_add`
  (two points `p ≠ q` span the line `{p, q, p+q}`) by `ZMod 2` arithmetic
  (`p + p = 0`).  The threshold reduces to a counting argument via
  `Finset.card_sdiff` against `Pts.card = 7`.
* Analysis (Analyst): both directions of the iff funnel through *one* bridge —
  "`S` misses two distinct points  ↔  `S.card ≤ 5`".  Forward (blocking ⇒ large):
  a missing pair starves their common line.  Reverse (large ⇒ blocking): a starved
  line would force two missing points hence `card ≤ 5`.
* Critique (Critic): the statement is not vacuous — `Pts.card = 7 ≥ 6`, so strong
  blocking sets exist (`Corollaries.lean`).  The main theorem is not `decide`-only:
  it uses `card_sdiff`, an existence-of-two-elements argument, and field arithmetic
  over `ZMod 2`.  The spanning condition `≥ 2` is exactly faithful to "`S ∩ ℓ`
  spans the projective line `ℓ`".
* Synthesis (PI): `fano_strongBlocking_iff_six` is the headline; `isLine_add` and
  the counting bridge are the reusable engines exported to `Corollaries.lean`.
-/

open Finset

open FanoStrongBlocking












open FanoStrongBlocking in
theorem solution: Pts.card = 7 := by decide
