-- Prove2me | Definitions.Def_Geometry_GenusFormula
-- name    : Geometry_GenusFormula
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:12:55.661308+00:00
-- url     : https://prove2.me/theorems/d46020d5-ef03-4b4d-ac81-7c04e91261c0
-- title:
--   Aether Catalog definitions — Geometry_GenusFormula
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.GenusFormula`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/GenusFormula.lean by skeleton subtraction
import Mathlib
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


namespace Hilbert16

/-! ## Genus Formula -/

/-- The genus of a smooth projective plane curve of degree `d`.
    This equals `(d - 1) * (d - 2) / 2` by the degree-genus formula. -/
def planeCurveGenus (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2

/-- The Harnack bound: maximum number of connected components of the real locus
    of a smooth real projective plane curve of degree `d`. -/
def harnackBound (d : ℕ) : ℕ := planeCurveGenus d + 1


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

/-- An abstract real curve with degree, genus, and oval count data.
    The `bound` axiom encodes the topological fact (Smith–Thom inequality)
    that the number of ovals is at most `genus + 1`. -/
structure AbstractRealCurve where
  /-- Degree of the curve -/
  degree : ℕ
  /-- Number of connected components (ovals) of the real locus -/
  ovalCount : ℕ
  /-- The curve has degree at least 1 -/
  degree_pos : 0 < degree
  /-- Smith–Thom bound: oval count is at most genus + 1 -/
  bound : ovalCount ≤ planeCurveGenus degree + 1





end Hilbert16


