-- Prove2me | solution 1 for PosetFlow.ChainFrom.exists_map_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:47:49.998304+00:00
-- url     : https://prove2.me/submissions/d03813ca-0a71-4386-a6fb-3686adee9213

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





omit [DecidableEq P] [DecidableEq Q] in
@[simp] theorem mem_trace_carrier (f : P ↪o Q) (E : ChainFrom (f x) (f y)) {a : P} :
    a ∈ (trace f E).carrier ↔ f a ∈ E.carrier :=
  Finset.mem_preimage (hf := f.injective.injOn)











open ChainFrom






/-!
### Order-reflection is necessary

The two-element antichain maps injectively and monotonically into the two-element
chain, but the unique chain from `0` to `1` of the target is supported on the image
and is not the transport of any chain of the source, since the source has no chain
from one point to the other at all.
-/


open Antichain2










open PosetFlow in
omit [DecidableEq P] in
theorem solution(f : P ↪o Q) (E : ChainFrom (f x) (f y)) :
    (∃ C : ChainFrom x y, map f C = E) ↔ ∀ b ∈ E.carrier, b ∈ Set.range f := by
  constructor
  · rintro ⟨C, rfl⟩ b hb
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨a, rfl⟩
  · intro h
    refine ⟨trace f E, ?_⟩
    ext1
    apply Finset.Subset.antisymm
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
      exact (mem_trace_carrier f E).1 ha
    · intro b hb
      obtain ⟨a, rfl⟩ := h b hb
      exact Finset.mem_image_of_mem _ ((mem_trace_carrier f E).2 hb)
