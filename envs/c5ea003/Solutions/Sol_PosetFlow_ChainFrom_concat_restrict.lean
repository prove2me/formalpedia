-- Prove2me | solution 1 for PosetFlow.ChainFrom.concat_restrict
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:47:49.418162+00:00
-- url     : https://prove2.me/submissions/97a68fe4-4724-4484-9ca2-a5616037f766

-- Sol generated from Algebra/PosetFlow/ChainPoset.lean
import Mathlib
import Definitions.Def_Algebra_PosetFlow_ChainPoset
import Definitions.Def_Algebra_PosetFlow_OrderComplexEuler

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





theorem concat_carrier (C : ChainFrom x y) (D : ChainFrom y z) :
    (concat C D).carrier = C.carrier ∪ D.carrier := by
  rfl

theorem restrictLeft_carrier (E : ChainFrom x z) (hy : y ∈ E.carrier) :
    (restrictLeft E hy).carrier = E.carrier.filter (· ≤ y) := by
  rfl

theorem restrictRight_carrier (E : ChainFrom x z) (hy : y ∈ E.carrier) :
    (restrictRight E hy).carrier = E.carrier.filter (y ≤ ·) := by
  rfl

open PosetFlow in
theorem solution(E : ChainFrom x z) (hy : y ∈ E.carrier) :
    concat (restrictLeft E hy) (restrictRight E hy) = E := by
  ext1
  apply Finset.Subset.antisymm
  · intro a ha
    simp only [concat_carrier, restrictLeft_carrier, restrictRight_carrier,
      Finset.mem_union, Finset.mem_filter] at ha
    tauto
  · intro a ha
    simp only [concat_carrier, restrictLeft_carrier, restrictRight_carrier,
      Finset.mem_union, Finset.mem_filter]
    rcases E.total ha hy with h | h
    · exact Or.inl ⟨ha, h⟩
    · exact Or.inr ⟨ha, h⟩
