-- Prove2me | Theorems.Thm_PosetFlow_ChainFrom_exists_map_eq_iff
-- name    : PosetFlow.ChainFrom.exists_map_eq_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:49:10.654652+00:00
-- url     : https://prove2.me/theorems/fbbb23ea-a543-4223-b9ac-87e8c65d2a41
-- title:
--   A chain of `Q` between two points of `P` is the transport of a chain of `P` iff
-- statement:
--   A chain of `Q` between two points of `P` is the transport of a chain of `P` iff
--   it is supported on the image of `P`.
--
--   ```lean
--   theorem PosetFlow.ChainFrom.exists_map_eq_iff(f : P ↪o Q) (E : ChainFrom (f x) (f y)) :
--       (∃ C : ChainFrom x y, map f C = E) ↔ ∀ b ∈ E.carrier, b ∈ Set.range f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PosetFlow/OrderReflecting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PosetFlow/OrderReflecting.lean#L134

-- Thm stub generated from Algebra/PosetFlow/OrderReflecting.lean
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









omit [DecidableEq P] in

theorem PosetFlow.ChainFrom.exists_map_eq_iff(f : P ↪o Q) (E : ChainFrom (f x) (f y)) :
    (∃ C : ChainFrom x y, map f C = E) ↔ ∀ b ∈ E.carrier, b ∈ Set.range f := by sorry
