-- Prove2me | Definitions.Def_Algebra_PosetFlow_OrderComplexEuler
-- name    : Algebra_PosetFlow_OrderComplexEuler
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:37:35.79248+00:00
-- url     : https://prove2.me/theorems/0753313f-071d-4056-bc0a-9be8cdfcb707
-- title:
--   Aether Catalog definitions — Algebra_PosetFlow_OrderComplexEuler
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PosetFlow.OrderComplexEuler`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PosetFlow/OrderComplexEuler.lean by skeleton subtraction
import Mathlib

/-!
# The order complex of a finite poset and cone points

This file develops the combinatorial (Euler-characteristic) shadow of the statement
"the simplicial nerve of a poset with a least element is contractible", which is the
homotopical engine behind the *chain replacement of a poset flow*: the poset of
strictly increasing chains from `x` to `y` ordered by refinement has a least element
(the chain `{x, y}`), hence its nerve is contractible, hence the chain replacement of
a poset flow has contractible spaces of execution paths.

Since simplicial contractibility is not available at this level of the library, we
prove the exact numerical consequence: the (unreduced) alternating face sum of the
order complex of a finite poset possessing a *cone point* vanishes, i.e. the reduced
Euler characteristic of the order complex is `0`.  The proof is a sign-reversing
involution: adding or deleting the cone point.

## Main definitions

* `PosetFlow.IsOrderChain` : a finset of a poset is totally ordered.
* `PosetFlow.orderComplex` : the finset of all totally ordered finsets (the faces of
  the order complex, including the empty face).

## Main results

* `PosetFlow.alternatingSum_orderComplex_eq_zero_of_conePoint` : if some element of a
  finite poset is comparable with every element, the alternating sum
  `∑ (-1) ^ |C|` over all faces `C` vanishes.
* `PosetFlow.reducedEuler_eq_zero_of_conePoint` : the reduced form, a sum over
  nonempty faces equal to `-1`.
* `PosetFlow.alternatingSum_orderComplex_eq_zero_of_orderBot` /
  `..._of_orderTop` : the special cases of a least / greatest element.
-/

namespace PosetFlow

open Finset

variable {R : Type*} [PartialOrder R] [Fintype R] [DecidableEq R] [DecidableLE R]

/-- A finset of a poset is a *chain* when it is totally ordered by the ambient order. -/
def IsOrderChain (C : Finset R) : Prop := ∀ a ∈ C, ∀ b ∈ C, a ≤ b ∨ b ≤ a

instance (C : Finset R) : Decidable (IsOrderChain C) := by
  unfold IsOrderChain; infer_instance



/-- The faces of the order complex of a finite poset: all totally ordered finsets
(the empty face included). -/
def orderComplex (R : Type*) [PartialOrder R] [Fintype R] [DecidableEq R] [DecidableLE R] :
    Finset (Finset R) :=
  Finset.univ.filter IsOrderChain







end PosetFlow


