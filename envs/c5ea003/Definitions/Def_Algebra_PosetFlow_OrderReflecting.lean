-- Prove2me | Definitions.Def_Algebra_PosetFlow_OrderReflecting
-- name    : Algebra_PosetFlow_OrderReflecting
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:48:33.705718+00:00
-- url     : https://prove2.me/theorems/0748c8ca-3331-4023-b9da-a2e590990dd4
-- title:
--   Aether Catalog definitions — Algebra_PosetFlow_OrderReflecting
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PosetFlow.OrderReflecting`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PosetFlow/OrderReflecting.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_PosetFlow_ChainPoset

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

namespace PosetFlow

open Finset

section Embedding

variable {P Q : Type*} [PartialOrder P] [PartialOrder Q] [DecidableEq P] [DecidableEq Q]
variable {x y : P}

namespace ChainFrom

/-- The chain of `Q` obtained by transporting a chain of `P` along an order
embedding. -/
def map (f : P ↪o Q) (C : ChainFrom x y) : ChainFrom (f x) (f y) where
  carrier := C.carrier.image f
  mem_source := Finset.mem_image_of_mem _ C.mem_source
  mem_target := Finset.mem_image_of_mem _ C.mem_target
  bounded := by
    rintro _ hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨f.map_rel_iff.2 (C.bounded ha).1, f.map_rel_iff.2 (C.bounded ha).2⟩
  total := by
    rintro u hu v hv
    obtain ⟨a, hamem, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨b, hbmem, rfl⟩ := Finset.mem_image.1 hv
    rcases C.total hamem hbmem with h | h
    · exact Or.inl (f.map_rel_iff.2 h)
    · exact Or.inr (f.map_rel_iff.2 h)



/-- **The trace of a chain of `Q` along an order-reflecting inclusion.**  Only here
is order-reflection used: without it the intersection of a chain of `Q` with the
image of `P` need not be a chain of `P`. -/
noncomputable def trace (f : P ↪o Q) (E : ChainFrom (f x) (f y)) : ChainFrom x y where
  carrier := E.carrier.preimage f (f.injective.injOn)
  mem_source := Finset.mem_preimage.2 E.mem_source
  mem_target := Finset.mem_preimage.2 E.mem_target
  bounded := by
    intro a ha
    rw [Finset.mem_preimage] at ha
    exact ⟨f.map_rel_iff.1 (E.bounded ha).1, f.map_rel_iff.1 (E.bounded ha).2⟩
  total := by
    intro a ha b hb
    rw [Finset.mem_preimage] at ha hb
    rcases E.total ha hb with h | h
    · exact Or.inl (f.map_rel_iff.1 h)
    · exact Or.inr (f.map_rel_iff.1 h)











end ChainFrom

open ChainFrom





end Embedding

/-!
### Order-reflection is necessary

The two-element antichain maps injectively and monotonically into the two-element
chain, but the unique chain from `0` to `1` of the target is supported on the image
and is not the transport of any chain of the source, since the source has no chain
from one point to the other at all.
-/

/-- The two-element antichain. -/
inductive Antichain2 : Type
  | a : Antichain2
  | b : Antichain2
  deriving DecidableEq

namespace Antichain2

instance : PartialOrder Antichain2 where
  le u v := u = v
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h _ := h


/-- The injective monotone (but not order-reflecting) comparison map to the
two-element chain. -/
def toChain2 : Antichain2 → Fin 2
  | a => 0
  | b => 1




end Antichain2


end PosetFlow


