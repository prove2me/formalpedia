-- Prove2me | Definitions.Def_Novelty_FanoStrongBlocking
-- name    : Novelty_FanoStrongBlocking
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:25:10.186184+00:00
-- url     : https://prove2.me/theorems/037a9b51-7472-40b4-87fc-ad1f92f1e3fd
-- title:
--   Aether Catalog definitions — Novelty_FanoStrongBlocking
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FanoStrongBlocking`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FanoStrongBlocking.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Fano-plane threshold for (additive) strong blocking sets, `h = 1` case

A **strong blocking set** (also *cutting blocking set*) of a projective space `PG(N, q)`
is a set of points that meets every hyperplane in a *spanning* subset of that hyperplane.
Strong blocking sets are exactly the geometric duals of **minimal linear codes**, and the
*additive* variant over `GF(q^h)` specialises, in the `h = 1` case, to the ordinary
(`GF(q)`-linear) strong blocking sets.  This file treats the smallest non-degenerate
projective plane, the **Fano plane** `PG(2, 2)` (`q = 2`, `N = 2`).

In a projective *plane* every hyperplane is a *line* (a `1`-dimensional projective subspace),
which is spanned by any two of its distinct points.  Hence a strong blocking set of a plane
is precisely a set meeting **every line in at least two points** (a *double blocking set*).

## Model

We use the cyclic (Singer) model of the Fano plane:

* points  `= ZMod 7`;
* lines   `= {i, i+1, i+3}` for `i : ZMod 7`,

which is the development of the perfect difference set `{0, 1, 3} (mod 7)`.

## Main results

* `FanoStrongBlocking.fanoLine_card` — every line has exactly `3` points.
* `FanoStrongBlocking.two_points_collinear` — any two distinct points lie on a common line
  (the projective-plane incidence axiom for this model).
* `FanoStrongBlocking.sb6_isStrongBlocking` — the `6`-point set `univ \ {0}` is a strong
  blocking set, witnessing the upper bound.
* `FanoStrongBlocking.strongBlocking_card_ge_six` — every strong blocking set has `≥ 6`
  points (the lower bound).
* `FanoStrongBlocking.fano_threshold_isLeast` — the minimum size of a strong blocking set of
  the Fano plane is exactly `6`.
* `FanoStrongBlocking.fano_threshold_eq_formula` — `6 = (k-1)(q+1)` for `k = 3`, `q = 2`,
  realising with equality the general strong-blocking-set lower bound `(k-1)(q+1)`.

## Catalog connections

* `Mathlib.Data.ZMod.Basic`, `Mathlib.Data.Finset.Card` supply the finite-incidence
  combinatorics.
* The `(k-1)(q+1)` formula links this plane instance to the general minimal-code /
  strong-blocking-set lower bound of Alfarano–Borello–Neri and Davydov–Giulietti–Marcugini–
  Pambianco; the Fano plane realises the bound with equality.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): In the `h = 1` (linear) case, an additive strong blocking set of
  `PG(2, q)` is a double blocking set, and for the Fano plane `q = 2` its minimum size should
  equal the general lower bound `(k-1)(q+1) = 2·3 = 6`, i.e. the bound is *tight* in the
  smallest plane.
Experiment (Experimenter): Modelled the Fano plane cyclically (`ZMod 7`, lines `{i,i+1,i+3}`).
  A brute-force enumeration of all `2^7 = 128` point sets (via `decide`) confirmed: (a) every
  line has `3` points; (b) `univ \ {0}` blocks every line twice; (c) NO set of size `≤ 5`
  blocks every line twice; hence the threshold is exactly `6`.
Analysis (Analyst): The lower bound has a clean conceptual proof: if `S` meets every line in
  `≥ 2` of its `3` points, its complement `T` meets every line in `≤ 1` point; but in the Fano
  plane *any two distinct points are collinear* (`two_points_collinear`), so `T` cannot contain
  two points — `|T| ≤ 1`, whence `|S| ≥ 6`.  This is the plane shadow of the general
  `(k-1)(q+1)` bound, here attained with equality.
Critique (Critic): The headline numbers (`3`, `6`) are finite checks; the load-bearing
  mathematical statement is the incidence axiom `two_points_collinear` together with the
  tightness identity `6 = (k-1)(q+1)`, which is what certifies that the Fano plane *saturates*
  the general strong-blocking-set bound rather than merely satisfying it.  Future cycles should
  test whether saturation persists for `PG(2, q)`, `q > 2`, where double-blocking minima are
  known to *exceed* `2(q+1)`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace FanoStrongBlocking

open Finset

/-- The `i`-th line of the cyclic (Singer) model of the Fano plane `PG(2,2)`:
the development of the perfect difference set `{0,1,3} (mod 7)`. -/
def fanoLine (i : ZMod 7) : Finset (ZMod 7) := {i, i + 1, i + 3}

/-- A set of points is a **strong blocking set** of the Fano plane iff it meets every line in
at least two points (equivalently, in a spanning subset of the line). -/
def IsStrongBlocking (S : Finset (ZMod 7)) : Prop :=
  ∀ i : ZMod 7, 2 ≤ (fanoLine i ∩ S).card



/-- The explicit `6`-point witness `univ \ {0}`. -/
def sb6 : Finset (ZMod 7) := Finset.univ \ {0}








end FanoStrongBlocking


