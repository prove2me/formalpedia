-- Prove2me | Theorems.Thm_PosetFlow_alternatingSum_openInterval_eq_neg_mu
-- name    : PosetFlow.alternatingSum_openInterval_eq_neg_mu
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:49:21.846725+00:00
-- url     : https://prove2.me/theorems/509c80bc-70bf-42f9-bcfe-9320dbf83dbf
-- title:
--   The Möbius function as a reduced Euler characteristic.
-- statement:
--   **The Möbius function as a reduced Euler characteristic.**  For `x < y` in a
--   finite poset, the alternating sum over the faces of the order complex of the open
--   interval `(x, y)` (the empty face included) equals `-μ x y`.
--
--   ```lean
--   theorem PosetFlow.alternatingSum_openInterval_eq_neg_mu(hxy : x < y) :
--       ∑ F ∈ orderComplex (openInterval x y), (-1 : ℤ) ^ F.card = -mu ℤ x y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PosetFlow/IntervalEuler.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PosetFlow/IntervalEuler.lean#L92

-- Thm stub generated from Algebra/PosetFlow/IntervalEuler.lean
import Mathlib
import Definitions.Def_Algebra_PosetFlow_HallMobius
import Definitions.Def_Algebra_PosetFlow_IntervalEuler
import Definitions.Def_Algebra_PosetFlow_OrderComplexEuler

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

open PosetFlow

open Finset IncidenceAlgebra

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P]
variable [LocallyFiniteOrder P]


variable {x y : P}

theorem PosetFlow.alternatingSum_openInterval_eq_neg_mu(hxy : x < y) :
    ∑ F ∈ orderComplex (openInterval x y), (-1 : ℤ) ^ F.card = -mu ℤ x y := by sorry
