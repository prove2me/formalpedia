-- Prove2me | solution 1 for PosetFlow.mem_orderComplex
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:48:00.889388+00:00
-- url     : https://prove2.me/submissions/4d9c172e-6722-4c79-968c-358a1354aca6

-- Sol generated from Algebra/PosetFlow/OrderComplexEuler.lean
import Mathlib
import Definitions.Def_Algebra_PosetFlow_OrderComplexEuler

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

open PosetFlow

open Finset

variable {R : Type*} [PartialOrder R] [Fintype R] [DecidableEq R] [DecidableLE R]













open PosetFlow in
@[simp] theorem solution{C : Finset R} : C ∈ orderComplex R ↔ IsOrderChain C := by
  simp [orderComplex]
