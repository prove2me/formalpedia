-- Prove2me | solution 1 for PosetFlow.ChainFrom.restrictRight_concat
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T23:11:53.717985+00:00
-- url     : https://prove2.me/submissions/4ca567a0-6151-4f78-a76a-bc9ba0e9e405

-- Sol generated from Algebra/PosetFlow/ChainPoset.lean
import Mathlib
import Definitions.Def_Algebra_PosetFlow_ChainPoset
import Definitions.Def_Algebra_PosetFlow_OrderComplexEuler
import Theorems.Thm_PosetFlow_ChainFrom_mem_concat_middle

/-!
# The refinement poset of strictly increasing chains of a poset

This file formalises the combinatorial core of the *chain replacement of a poset
flow*.  For a poset `P` and `x y : P`, the paper considers the poset of strictly
increasing chains from `x` to `y`, ordered by refinement, and takes its simplicial
nerve as the space of execution paths from `x` to `y` of the replacement flow.

Here a chain from `x` to `y` is recorded by its underlying finite set
(`PosetFlow.ChainFrom x y`): a finite, totally ordered subset of `P` containing `x`
and `y` and contained in the interval `[x, y]`.  Refinement is inclusion of
carriers.  We prove:

* `PosetFlow.ChainFrom.bot_le` : the chain `{x, y}` is the least element, so the
  refinement poset is a cone.  This is why the chain replacement of a poset flow is
  a *replacement*: its path spaces are contractible.
* `PosetFlow.alternatingSum_chainFrom_eq_zero` : the Euler-characteristic shadow of
  that contractibility, obtained from `OrderComplexEuler`.
* `PosetFlow.ChainFrom.concat` and `PosetFlow.ChainFrom.concat_assoc` : the
  composition law of the chain replacement (a poset-enriched semicategory
  structure), which is monotone in each variable.
* `PosetFlow.chainSplitOrderIso` : the *unique factorisation* of a chain through an
  intermediate point, as an order isomorphism
  `{E : ChainFrom x z // y ∈ E} ≃o ChainFrom x y × ChainFrom y z`.  This is the
  combinatorial statement which, at the level of flows, says that concatenation
  identifies path spaces of composites.
-/

open PosetFlow

open Finset

variable {P : Type*} [PartialOrder P] [DecidableEq P] [DecidableLE P]


open ChainFrom

variable {x y z w : P}






























open ChainFrom





theorem concat_carrier {P : Type*} [PartialOrder P] [DecidableEq P] [DecidableLE P] {x y z : P} (C : ChainFrom x y) (D : ChainFrom y z) : (concat C D).carrier = C.carrier ∪ D.carrier := rfl
theorem restrictRight_carrier {P : Type*} [PartialOrder P] [DecidableEq P] [DecidableLE P] {x y z : P} (E : ChainFrom x z) {y : P} (hy : y ∈ E.carrier) (a : P) : a ∈ (restrictRight E hy).carrier ↔ a ∈ E.carrier ∧ y ≤ a := by rw [show (restrictRight E hy).carrier = E.carrier.filter (y ≤ ·) from rfl, Finset.mem_filter]
open PosetFlow in
theorem solution(C : ChainFrom x y) (D : ChainFrom y z) :
    restrictRight (concat C D) (mem_concat_middle C D) = D := by
  ext1
  apply Finset.Subset.antisymm
  · intro a ha
    have h1 : a ∈ (concat C D).carrier ∧ y ≤ a := Finset.mem_filter.1 ha
    rcases Finset.mem_union.1 h1.1 with h | h
    · have : a = y := le_antisymm (C.bounded h).2 h1.2
      exact this ▸ D.mem_source
    · exact h
  · intro a ha
    exact Finset.mem_filter.2 ⟨Finset.mem_union_right _ ha, (D.bounded ha).1⟩
