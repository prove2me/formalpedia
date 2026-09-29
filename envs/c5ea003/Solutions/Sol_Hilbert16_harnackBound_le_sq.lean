-- Prove2me | solution 1 for Hilbert16.harnackBound_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:16:03.64137+00:00
-- url     : https://prove2.me/submissions/d4ee3971-db0d-4a16-beaa-90b3129a6d53

-- Sol generated from Geometry/GenusFormula.lean
import Mathlib
import Definitions.Def_Geometry_GenusFormula
/-
# Genus Formula and Harnack Bound for Real Plane Algebraic Curves

This file formalizes the genus formula for smooth projective plane curves
and proves the Harnack bound on the number of connected components (ovals)
of their real locus.

## Main definitions

* `planeCurveGenus d` — The genus of a smooth projective plane curve of degree `d`,
  equal to `(d - 1) * (d - 2) / 2`.

* `harnackBound d` — The maximum number of connected components of the real locus
  of a smooth real projective plane curve of degree `d`, equal to `genus + 1`.

## Main results

* `harnackBound_eq` — `harnackBound d = (d - 1) * (d - 2) / 2 + 1`
* Explicit values for degrees 1 through 8
* `planeCurveGenus_pos` — genus is positive for degree ≥ 3
* `planeCurveGenus_succ` — recurrence relation g(d+1) = g(d) + (d-1)
* `harnackBound_le_sq` — growth bound `harnackBound d ≤ d * d`

## Mathematical context

For a smooth real projective plane curve of degree `d`, the complex curve is a
compact Riemann surface of genus `g = (d-1)(d-2)/2`. Complex conjugation acts
as an anti-holomorphic involution, and the real locus is its fixed point set.
By Smith–Thom theory, the number of connected components of the fixed point set
of an involution on a genus-`g` surface is at most `g + 1`. This is the Harnack
bound, first proved by Axel Harnack in 1876.
-/


open Hilbert16

/-! ## Genus Formula -/




/-! ## Genus values for small degrees -/


/-! ## Harnack bound values for small degrees -/


/-! ## Properties of the genus formula -/




/-
The genus formula satisfies the recurrence g(d+1) = g(d) + (d-1) for d ≥ 2.
-/

/-
The Harnack bound is at most d²/2 + 1 ≤ d² for d ≥ 2.
-/

/-! ## Abstract Harnack bound structure

We define an abstract structure capturing curves with genus and oval count,
and prove that the Harnack bound follows from the genus formula. -/







open Hilbert16 in
theorem solution(d : ℕ) (hd : 2 ≤ d) : harnackBound d ≤ d * d := by
  unfold harnackBound planeCurveGenus;
  nlinarith [ Nat.div_mul_le_self ( ( d - 1 ) * ( d - 2 ) ) 2, Nat.sub_le d 1, Nat.sub_le d 2 ]
