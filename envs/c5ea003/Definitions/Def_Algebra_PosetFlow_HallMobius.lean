-- Prove2me | Definitions.Def_Algebra_PosetFlow_HallMobius
-- name    : Algebra_PosetFlow_HallMobius
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:45:09.626394+00:00
-- url     : https://prove2.me/theorems/17a68ab2-e20d-49cf-890c-6baad6057407
-- title:
--   Aether Catalog definitions — Algebra_PosetFlow_HallMobius
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PosetFlow.HallMobius`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PosetFlow/HallMobius.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_PosetFlow_ChainPoset

/-!
# Philip Hall's theorem: chains of a poset compute its Möbius function

The chain replacement of a poset flow replaces the (one point) spaces of execution
paths of a poset flow by the nerves of the refinement posets of chains.  The Euler
characteristics of those nerves are governed by the classical theorem of Philip
Hall, which identifies the alternating sum over chains from `x` to `y` with the
Möbius function of the incidence algebra.

This file proves Hall's theorem in the form

`∑ C ∈ chainFinsets x y, (-1) ^ |C| = - μ x y`,

where `chainFinsets x y` is the finite set of carriers of chains from `x` to `y`
(the objects of the refinement poset `PosetFlow.ChainFrom x y` of
`Algebra.PosetFlow.ChainPoset`), and `μ` is `IncidenceAlgebra.mu`.

## Main results

* `PosetFlow.chainAltSum_recursion` : deleting the top element `y` of a chain
  identifies chains from `x` to `y` with pairs `(z, C)` where `z ∈ Ico x y` and `C`
  is a chain from `x` to `z`.  This is the combinatorial induction step.
* `PosetFlow.chainAltSum_eq_neg_mu` : **Philip Hall's theorem**.
* `PosetFlow.mu_eq_zero_of_not_le` : the Möbius function vanishes off the order,
  a corollary of the chain description.
-/

namespace PosetFlow

open Finset IncidenceAlgebra

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P]

/-- The carriers of the chains from `x` to `y`, as a finite set of finsets. -/
def chainFinsets (x y : P) : Finset (Finset P) :=
  Finset.univ.filter fun C =>
    x ∈ C ∧ y ∈ C ∧ (∀ a ∈ C, x ≤ a ∧ a ≤ y) ∧ (∀ a ∈ C, ∀ b ∈ C, a ≤ b ∨ b ≤ a)



/-- The alternating sum over the chains from `x` to `y`. -/
def chainAltSum (x y : P) : ℤ := ∑ C ∈ chainFinsets x y, (-1 : ℤ) ^ C.card






section Recursion

variable [LocallyFiniteOrder P]




end Recursion

end PosetFlow


