-- Prove2me | Definitions.Def_Algebra_PosetFlow_IntervalEuler
-- name    : Algebra_PosetFlow_IntervalEuler
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:47:56.556064+00:00
-- url     : https://prove2.me/theorems/d60ffe4c-e899-4834-922f-81a90b592ec0
-- title:
--   Aether Catalog definitions — Algebra_PosetFlow_IntervalEuler
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PosetFlow.IntervalEuler`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PosetFlow/IntervalEuler.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_PosetFlow_HallMobius

/-!
# The Möbius function is the reduced Euler characteristic of the open interval

This file synthesises the two main computations of this development:

* `PosetFlow.alternatingSum_orderComplex_eq_zero_of_conePoint` (a cone is acyclic),
* `PosetFlow.chainAltSum_eq_neg_mu` (Philip Hall's theorem).

Removing the two endpoints identifies the chains from `x` to `y` with the faces of
the order complex of the open interval `(x, y)`.  Hence Hall's theorem becomes the
classical statement that the Möbius function of an interval is (up to sign) the
reduced Euler characteristic of the order complex of its interior, and the cone
argument yields a vanishing criterion for the Möbius function.

## Main results

* `PosetFlow.alternatingSum_openInterval_eq_neg_mu` : for `x < y` in a finite poset,
  the alternating face sum of the order complex of the open interval `(x, y)` is
  `-μ x y`.
* `PosetFlow.mu_eq_zero_of_conePoint_openInterval` : if the open interval `(x, y)`
  has an element comparable with all of its elements, then `μ x y = 0`.  In
  particular this applies to the refinement posets of chains of the chain
  replacement, whose least element is a cone point.
-/

namespace PosetFlow

open Finset IncidenceAlgebra

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P]
variable [LocallyFiniteOrder P]

/-- The open interval `(x, y)` of a finite poset, as a type. -/
abbrev openInterval (x y : P) : Type _ := {a : P // a ∈ Finset.Ioo x y}

variable {x y : P}

/-- Adjoining the two endpoints to a face of the order complex of the open interval
`(x, y)` produces a chain from `x` to `y`. -/
private def addEnds (x y : P) (F : Finset (openInterval x y)) : Finset P :=
  insert x (insert y (F.image Subtype.val))






end PosetFlow


