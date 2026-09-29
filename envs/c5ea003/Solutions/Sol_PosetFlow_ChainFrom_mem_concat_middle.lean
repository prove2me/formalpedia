-- Prove2me | solution 1 for PosetFlow.ChainFrom.mem_concat_middle
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:48:00.306187+00:00
-- url     : https://prove2.me/submissions/01937572-0d75-476e-b75e-a031e78bbb50

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





open PosetFlow.ChainFrom in
omit [DecidableLE P] in
theorem solution(C : ChainFrom x y) (D : ChainFrom y z) :
    y ∈ (concat C D).carrier := Finset.mem_union_left _ C.mem_target
