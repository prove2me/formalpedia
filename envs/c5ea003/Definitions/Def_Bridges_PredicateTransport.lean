-- Prove2me | Definitions.Def_Bridges_PredicateTransport
-- name    : Bridges_PredicateTransport
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T10:39:40.084624+00:00
-- url     : https://prove2.me/theorems/1673087d-f847-415f-a193-15fc060af093
-- title:
--   Aether Catalog definitions — Bridges_PredicateTransport
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PredicateTransport`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PredicateTransport.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_ComposableTransfer
import Definitions.Def_Bridges_TheoryMorphisms
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Predicate Transport Along Invariant-Preserving Morphisms

This file establishes a general calculus of **predicate transport** across
theory morphisms. The central abstraction is `InvariantDetermined`: a
predicate on a theory's carrier that depends only on the invariant value.
Such predicates factor through the invariant, transport covariantly along
morphisms (existential push-forward), and pull back contravariantly
(universal pullback). Lower and upper bound predicates become special cases.

## Main Definitions

* `InvariantDetermined T P` — `P` depends only on `T.Inv`
* `PredicateFactorsThroughInvariant T P` — `P` factors as `R ∘ T.Inv`
* `TransferablePredicate f P Q` — `f` maps `P`-witnesses to `Q`-witnesses
* `SatisfiesLowerBound T n` / `SatisfiesUpperBound T n` — threshold predicates
* `InvariantPredicatePush f R` — push an invariant-side predicate to the codomain

## Main Results

* `invariantDetermined_iff_factorsThroughInvariant` — characterization
* `transferablePredicate_exists` — existential transport
* `TransferablePredicate.id` / `.comp` — functoriality
* `satisfiesLowerBound_invariantDetermined` — lower bounds are invariant-determined
* `satisfiesUpperBound_invariantDetermined` — upper bounds are invariant-determined
* `certified_lower_bound_transfer_via_predicates` — old theorem as corollary
* `invariant_determined_transfer` — invariant-determined predicates are stable
* `upper_bound_pullback` — contravariant transport of upper bounds
* `forall_pullback_of_transfer` — universal pullback principle
* `transferablePredicate_exists_comp` — compositional existential transport

## Design Philosophy

This replaces isolated transfer lemmas with a reusable transport machine.
Any property determined by an invariant automatically inherits transfer,
composition, and duality properties. The old `transfer_lower_bound` theorem
becomes a one-line corollary.
-/


/-! ## §1. Invariant-Determined Predicates -/

/-- A predicate `P` on a theory's carrier is **invariant-determined** if
    objects with equal invariant values satisfy `P` iff each other does.
    This is the right notion of "P factors through the invariant." -/
def InvariantDetermined (T : ResearchTheory) (P : T.Carrier → Prop) : Prop :=
  ∀ ⦃x y : T.Carrier⦄, T.Inv x = T.Inv y → (P x ↔ P y)

/-- A predicate **factors through the invariant** if there exists a predicate
    `R` on `ℕ` (the invariant type) such that `P x ↔ R (T.Inv x)` for all `x`. -/
def PredicateFactorsThroughInvariant (T : ResearchTheory) (P : T.Carrier → Prop) : Prop :=
  ∃ R : ℕ → Prop, ∀ x, P x ↔ R (T.Inv x)

/-
**Key characterization**: a predicate is invariant-determined if and only if
    it factors through the invariant. This identifies the semantic class of
    transportable predicates as those living on invariant space.
-/

/-! ## §2. Transferable Predicates -/

/-- A predicate `P` on `T` is **transferable** to `Q` on `U` along `f`
    if every `P`-witness maps to a `Q`-witness. This is the fundamental
    unit of predicate transport. -/
def TransferablePredicate
    {T U : ResearchTheory} (f : TheoryHom T U)
    (P : T.Carrier → Prop) (Q : U.Carrier → Prop) : Prop :=
  ∀ x, P x → Q (f.toFun x)

/-
**Existential transport**: transferable predicates push forward existence.
-/

/-! ## §3. Functoriality of Transferable Predicates -/

/-
**Identity**: every predicate is transferable to itself along the identity.
-/

/-
**Composition**: transferable predicates compose along morphism chains.
-/

/-
**Compositional existential transport**: existence witnesses survive
    composed transfers. Combines composition with existential transport.
-/

/-! ## §4. Lower and Upper Bound Predicates -/

/-- An element **satisfies the lower bound** `n` if its invariant is ≥ `n`.
    Note: this is a pointwise predicate, complementing the existential
    `SatisfiesLowerBound` from `TheoryMorphisms`. -/
def SatisfiesLowerBoundPred (T : ResearchTheory) (n : ℕ) : T.Carrier → Prop :=
  fun x => n ≤ T.Inv x

/-- An element **satisfies the upper bound** `n` if its invariant is ≤ `n`. -/
def SatisfiesUpperBound (T : ResearchTheory) (n : ℕ) : T.Carrier → Prop :=
  fun x => T.Inv x ≤ n

/-
Lower-bound predicates are invariant-determined.
-/

/-
Upper-bound predicates are invariant-determined.
-/

/-! ## §5. Lower Bound Transfer as a Corollary -/

/-
**Lower bound transfer via the predicate framework**: the monotonicity
    of theory morphisms makes lower-bound predicates transferable.
    This subsumes the old `transfer_lower_bound` theorem.
-/


/-! ## §6. Invariant Predicate Push and Transport -/


/-
**Invariant predicate transport for exact morphisms**: when a morphism
    preserves invariants exactly (not just monotonically), every
    invariant-determined predicate induces a transferable predicate pair
    via its factorization through the invariant.

    Note: this requires exact invariant preservation (`U.Inv (f.toFun x) = T.Inv x`),
    which is stronger than the monotonicity in `TheoryHom`. For the general
    monotone case, see `invariant_determined_transfer` which uses a different
    construction.
-/

/-
**Invariant-determined transfer**: invariant-determined predicates on `T`
    produce invariant-determined transferable predicates on `U`.
    The transported predicate is itself invariant-determined.
-/

/-! ## §7. Contravariant Transport: Universal Pullback -/

/-
**Universal pullback principle**: universal properties pull back
    along any map. If every element of `U` satisfies `Q`, then every
    element in the image of `f` satisfies `Q`.
-/

/-
**Upper bound pullback**: if every element of `U` has invariant ≤ `n`,
    then every element of `T` has invariant ≤ `n` (via the monotonicity
    of the morphism). This is the contravariant dual of lower-bound
    pushforward.
-/


/-! ## §8. Boolean Closure of Invariant-Determined Predicates -/

/-
Invariant-determined predicates are closed under conjunction.
-/

/-
Invariant-determined predicates are closed under disjunction.
-/

/-
Invariant-determined predicates are closed under negation.
-/

/-
Invariant-determined predicates are closed under implication.
-/

/-
Invariant-determined predicates are closed under biconditional.
-/

/-! ## §9. Connecting to ComposableTransfer -/


/-! ## §10. Cross-Domain Instantiation: Recovering Existing Theorems -/




/-
**Exact value predicates are invariant-determined**: the predicate
    `T.Inv x = n` is invariant-determined.
-/


