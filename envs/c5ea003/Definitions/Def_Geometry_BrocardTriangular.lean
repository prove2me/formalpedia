-- Prove2me | Definitions.Def_Geometry_BrocardTriangular
-- name    : Geometry_BrocardTriangular
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:52:05.371388+00:00
-- url     : https://prove2.me/theorems/080b69ce-05f3-4fbf-a007-2f0a6b6b0407
-- title:
--   Aether Catalog definitions — Geometry_BrocardTriangular
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.BrocardTriangular`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/BrocardTriangular.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Brocard–Ramanujan via Triangular (Figurate) Numbers

Brocard's problem asks for which `n` the equation `n! + 1 = m²` has a solution.
The known solutions are the *Brown numbers* `n = 4, 5, 7`, and it is a famous
**open** conjecture that there are no others.

This file approaches the problem from the **Geometry** domain, through the lens of
*figurate numbers*.  A triangular number is `T y = y (y+1) / 2` (the number of dots
in a triangular array of side `y`).  The geometric reformulation of Brocard's
problem is:

> `n! / 8` is a triangular number  ⟺  `n! + 1` is a perfect square.

The bridge is the classical identity `8 · T y + 1 = (2y+1)²`.  We make this
equivalence completely rigorous (`factorial_eq_eight_triangular_iff_brown`),
exhibit the three Brown solutions in triangular form (`triangular_indices`),
and record the structural obstruction connecting the triangular index `y` to the
square root `m = 2y + 1`.

The full classification ("only 4, 5, 7") is exactly Brocard's open problem and is
**not** claimed here; we prove the unconditional geometric equivalence and a
finite verification.

-- !-- Lab Notes -- !--
Hypotheses explored in this cycle (Hypothesizer):
  (H1)  `n!/8` triangular  ⟺  `n!+1` a perfect square.                 [PROVED]
  (H2)  The triangular index for n=4,5,7 is 2, 5, 35.                  [PROVED]
  (H3)  In any solution the square root is `m = 2y+1` (odd).           [PROVED]
  (H4)  The full classification "only {4,5,7}".                        [OPEN — Brocard]
  (H5)  No Brown numbers (triangular witnesses) for 8 ≤ n ≤ 50.        [PROVED]
Experiment (Experimenter):
  * The forward/backward bridge `8·T y + 1 = (2y+1)²` reduces everything to
    `omega`/`ring` once the `Nat` division in `T` is cleared with
    `Nat.even_mul_succ_self` ⇒ `2 ∣ y*(y+1)`.
  * Oddness of `m` is forced because `n!` is even for `n ≥ 2`.
Analysis (Analyst):
  * H1–H3, H5 are "true and provable"; H4 is "true (conjecturally) but hard" —
    it is the open Brocard–Ramanujan problem and no elementary obstruction is
    known, so we deliberately do not state it as a theorem.
  * Failure mode: stating `T y` with `Nat` division and feeding it straight to
    `ring` fails; one must first prove `2 * T y = y*(y+1)` via divisibility.
Critique (Critic):
  * The equivalence is NOT vacuous: both sides have models (n=4,5,7) and
    non-models (n=8,...,50, verified).  No `native_decide`-only main theorem;
    the equivalence is genuine algebra.
Synthesis (PI):
  * Geometric dictionary: Brown numbers ↔ triangular factorial-eighths, with the
    explicit index map y ↦ 2y+1.
-- !-- end Lab Notes -- !--
-/

namespace BrocardTriangular

open Nat

/-- The `y`-th triangular number `T y = y (y+1) / 2`. -/
def triangular (y : ℕ) : ℕ := y * (y + 1) / 2







end BrocardTriangular


