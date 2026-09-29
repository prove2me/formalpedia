-- Prove2me | solution 1 for PosetFlow.orderReflecting_necessary
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:54:40.632106+00:00
-- url     : https://prove2.me/submissions/a05ca946-28c9-42f6-a1d8-e40ff20fc639

-- Sol generated from Algebra/PosetFlow/OrderReflecting.lean
import Mathlib
import Definitions.Def_Algebra_PosetFlow_ChainPoset
import Definitions.Def_Algebra_PosetFlow_OrderReflecting

/-!
# Order-reflecting inclusions and the chain replacement

The paper *The chain replacement of a poset flow* shows that the chain replacement
sends inclusions of finite posets to q-cofibrations, and that pushouts along the
chain replacement of an **order-reflecting** inclusion preserve spaces of execution
paths.  This file isolates the combinatorial content of these statements at the
level of the refinement posets of chains, which are the (models of the) spaces of
execution paths.

An order-reflecting inclusion is exactly an `OrderEmbedding` `f : P ↪o Q`.

## Main results

* `PosetFlow.ChainFrom.trace_map` : the *trace* along `f` (intersecting a chain of
  `Q` with the image of `P` and pulling it back) is a monotone retraction of the
  monotone map induced by `f` on chain posets.  Order-reflection is what makes the
  trace well defined.
* `PosetFlow.chainGaloisCoinsertion` : more precisely, the induced map on chain
  posets and the trace form a **Galois coinsertion**.  Adjoint monotone maps induce
  homotopy equivalences of nerves, so this is the combinatorial reason the induced
  map of path spaces is so well behaved.
* `PosetFlow.ChainFrom.isLowerSet_range_map` : the image of the chain poset of `P`
  inside the chain poset of `Q` is a *lower set* for refinement (a sieve): a chain
  coarser than a chain coming from `P` again comes from `P`.  This is the
  cofibration-flavoured statement.
* `PosetFlow.chainOrderEmbedding` : the induced map of chain posets is an order
  embedding, and `PosetFlow.ChainFrom.map_concat` says it is compatible with the
  composition law of the chain replacement.
* `PosetFlow.chainSumEquiv` : the chain poset of `Q` is the disjoint union of the
  chains transported from `P` and those not supported on `P`; combined with the
  lower/upper set statements this is the combinatorial form of "pushouts along the
  chain replacement preserve spaces of execution paths".
* `PosetFlow.orderReflecting_necessary` : a counterexample showing that
  order-reflection cannot be weakened to injective monotonicity: for the inclusion
  of the two-element antichain into the two-element chain there are chains of the
  target entirely supported on the image which are not traces of any chain of the
  source.
-/

open PosetFlow

open Finset


variable {P Q : Type*} [PartialOrder P] [PartialOrder Q] [DecidableEq P] [DecidableEq Q]
variable {x y : P}

open ChainFrom
















open ChainFrom






/-!
### Order-reflection is necessary

The two-element antichain maps injectively and monotonically into the two-element
chain, but the unique chain from `0` to `1` of the target is supported on the image
and is not the transport of any chain of the source, since the source has no chain
from one point to the other at all.
-/


open Antichain2


theorem le_iff {u v : Antichain2} : u ≤ v ↔ u = v := Iff.rfl


theorem toChain2_injective : Function.Injective toChain2 := by
  intro u v h
  cases u <;> cases v <;> simp_all [toChain2]

theorem toChain2_monotone : Monotone toChain2 := by
  intro u v h
  rw [le_iff] at h
  exact le_of_eq (congrArg _ h)





open PosetFlow in
open PosetFlow in
theorem solution:
    Function.Injective Antichain2.toChain2 ∧ Monotone Antichain2.toChain2 ∧
      (∀ v ∈ (coarsest (show Antichain2.toChain2 Antichain2.a ≤ Antichain2.toChain2 Antichain2.b
          by decide)).carrier, v ∈ Set.range Antichain2.toChain2) ∧
      IsEmpty (ChainFrom Antichain2.a Antichain2.b) := by
  refine ⟨toChain2_injective, toChain2_monotone, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact ⟨Antichain2.a, rfl⟩
    · rw [Finset.mem_singleton] at hv
      subst hv
      exact ⟨Antichain2.b, rfl⟩
  · refine ⟨fun C => ?_⟩
    have := C.source_le_target
    rw [le_iff] at this
    exact absurd this (by decide)
