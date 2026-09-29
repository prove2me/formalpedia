-- Prove2me | Definitions.Def_Bridges_PosetTheory_RetrocausalLogic
-- name    : Bridges_PosetTheory_RetrocausalLogic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:23.336258+00:00
-- url     : https://prove2.me/theorems/05d9cf16-3eb0-4567-a54c-c79c8f8f53df
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_RetrocausalLogic
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.RetrocausalLogic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/RetrocausalLogic.lean by skeleton subtraction
import Mathlib
/-
# Retrocausal Mathematics: Where Effects Precede Causes

This module formalizes retrocausal mathematical structures where implications
can flow backward in time. We define temporal Galois connections on lattices,
prove that retrocausal closure operators arise naturally, and establish that
retrocausal logics are inherently intuitionistic.

## Main Definitions
- `TemporalGaloisConnection`: A Galois connection (T, R) on a lattice,
  modeling forward and backward temporal influence.
- `RetrocausalClosure`: The closure operator R ∘ T arising from the adjunction.
- `RetrocausalInterior`: The interior operator T ∘ R (dual).
- `CPTTriple`: A triple of involutions modeling charge, parity, and time reversal.

## Main Results
- `retrocausal_closure_is_closure`: R ∘ T is a closure operator.
- `retrocausal_interior_is_interior`: T ∘ R is an interior operator.
- `retrocausal_fixpoints_form_heyting`: Fixed points of the closure form
  a complete lattice (and hence support intuitionistic reasoning).
- `cpt_composition_involutive`: The composition C ∘ P ∘ T is an involution.
- `temporal_excluded_middle`: A temporal form of excluded middle holds
  for the closure operator.
-/


open OrderDual

/-! ## Temporal Galois Connections -/

/-- A temporal Galois connection on a lattice, modeling forward temporal
    propagation T and backward (retrocausal) propagation R as an adjoint pair.
    The adjunction T a ≤ b ↔ a ≤ R b captures that forward and backward
    time evolution are dual operations. -/
structure TemporalGaloisConnection (α : Type*) [Preorder α] where
  /-- Forward temporal propagation -/
  T : α → α
  /-- Retrocausal (backward) propagation -/
  R : α → α
  /-- The Galois connection: T is left adjoint to R -/
  gc : GaloisConnection T R

namespace TemporalGaloisConnection

variable {α : Type*} [Preorder α] (τ : TemporalGaloisConnection α)





end TemporalGaloisConnection

/-! ## Retrocausal Closure Operator -/

/-- The retrocausal closure operator R ∘ T. This sends each proposition to its
    "retrocausal completion" — the weakest proposition that is stable under
    the forward-backward temporal round trip. -/
def retrocausalClosure {α : Type*} [Preorder α] (τ : TemporalGaloisConnection α) : α → α :=
  τ.R ∘ τ.T

/-- The retrocausal interior operator T ∘ R. Dual to the closure. -/
def retrocausalInterior {α : Type*} [Preorder α] (τ : TemporalGaloisConnection α) : α → α :=
  τ.T ∘ τ.R

section ClosureProperties

variable {α : Type*} [PartialOrder α] (τ : TemporalGaloisConnection α)



/-
The retrocausal closure is idempotent: R(T(R(T(a)))) = R(T(a)).
    This is a key property showing that the closure stabilizes after one application.
    The proof uses the Galois connection adjunction essentially.
-/


/-
The retrocausal interior is idempotent: T(R(T(R(a)))) = T(R(a)).
-/

end ClosureProperties

/-! ## Lattice Properties of Temporal Operators -/

section LatticeProperties

variable {α : Type*} [CompleteLattice α] (τ : TemporalGaloisConnection α)

/-
Forward propagation preserves suprema (as a left adjoint).
    This is a fundamental property: temporal propagation distributes over disjunction.
-/

/-
Backward propagation preserves infima (as a right adjoint).
    Retrocausal propagation distributes over conjunction.
-/

/-
Forward propagation preserves ⊥.
    The temporal propagation of impossibility is impossible.
-/

/-
Backward propagation preserves ⊤.
    The retrocausal propagation of tautology is tautological.
-/

/-
Forward propagation preserves binary suprema.
-/

/-
Backward propagation preserves binary infima.
-/

end LatticeProperties

/-! ## Temporal Excluded Middle -/

section TemporalEM

variable {α : Type*} [BooleanAlgebra α] (τ : TemporalGaloisConnection α)

/-
**Temporal Excluded Middle**: For any proposition, its retrocausal closure
    joined with the retrocausal closure of its complement covers everything.
    This is a temporal analogue of the classical law of excluded middle, but
    it holds even when the underlying logic is intuitionistic — the closure
    operator "classicalizes" the temporal fragment.

    The key insight: R(T(a)) ⊔ R(T(aᶜ)) = ⊤ when the base algebra is Boolean.
    This follows because a ⊔ aᶜ = ⊤, and R ∘ T, being extensive and monotone,
    preserves this property in a Boolean algebra.
-/

end TemporalEM

/-! ## CPT Symmetry -/

/-- A CPT triple consists of three involutions (charge conjugation C, parity P,
    time reversal T) on a type, modeling the discrete symmetries of physics.
    The key requirement is that their composition is again an involution. -/
structure CPTTriple (α : Type*) where
  /-- Charge conjugation -/
  C : α → α
  /-- Parity reversal -/
  P : α → α
  /-- Time reversal -/
  T : α → α
  /-- C is an involution -/
  C_invol : ∀ a, C (C a) = a
  /-- P is an involution -/
  P_invol : ∀ a, P (P a) = a
  /-- T is an involution -/
  T_invol : ∀ a, T (T a) = a

namespace CPTTriple

variable {α : Type*} (cpt : CPTTriple α)

/-- The CPT composition -/
def compose : α → α := cpt.C ∘ cpt.P ∘ cpt.T

/-
Note: The converse of `cpt_involutive_of_commute` does NOT hold in general.
   Counterexample on Fin 3: C = swap(0,1), P = swap(0,2), T = swap(0,1).
   Then C∘P∘T = swap(1,2) which is an involution, but C and P do not commute.

The CPT composition reverses: if CPT is an involution, then CPT = TPC.
    This is an algebraic analogue of the CPT symmetry from quantum field theory.
-/

/-
When the three involutions commute, the CPT composition is an involution.
-/

end CPTTriple

/-! ## Retrocausal Fixed Points -/

/-- The set of retrocausal fixed points — propositions stable under the
    retrocausal closure. These are the "temporally complete" propositions. -/
def retrocausalFixedPoints {α : Type*} [Preorder α] (τ : TemporalGaloisConnection α) : Set α :=
  {a | retrocausalClosure τ a = a}

section FixedPointProperties

variable {α : Type*} [CompleteLattice α] (τ : TemporalGaloisConnection α)

/-
⊤ is a retrocausal fixed point.
-/

/-
The infimum of retrocausal fixed points is a retrocausal fixed point.
    This shows the fixed points form a complete lattice (by the Knaster-Tarski
    theorem applied to the closure operator).
-/


/-
An element is a fixed point iff it is in the range of R.
-/

end FixedPointProperties

/-! ## Retrocausal Monad Structure -/

section MonadStructure

variable {α : Type*} [PartialOrder α] (τ : TemporalGaloisConnection α)

/-
The retrocausal closure satisfies the monad multiplication law:
    R(T(R(T(a)))) ≤ R(T(a)). Combined with extensiveness, this gives
    idempotency for partial orders.
-/

/-
T ∘ R ∘ T = T. This is the "temporal coherence" law: propagating forward,
    then backward, then forward again is the same as propagating forward once.
-/

/-
R ∘ T ∘ R = R. The dual coherence law: backward propagation is insensitive
    to an intermediate forward-backward round trip.
-/

end MonadStructure

/-! ## Intuitionistic Character of Retrocausal Logic -/

section IntuitionisticCharacter

variable {α : Type*} [CompleteLattice α] (τ : TemporalGaloisConnection α)

/-
The retrocausal closure is super-additive: the closure of a join
    is at least the join of the closures. This is a general property
    of closure operators and shows that temporal completion is
    "optimistic" — it opens more possibilities than the parts suggest.
-/

/-
Key theorem: the retrocausal closure preserves finite meets on fixed points.
    This is what makes the fixed-point lattice a Heyting algebra
    (meet-semilattice with right adjoint to meet).
-/

end IntuitionisticCharacter

/-! ## Concrete Construction: Retrocausal Prop Lattice -/


/-
**Falsifiable Conjecture**: For any retrocausal Kripke frame with at least 3 worlds
    and a non-trivial retrocausal relation, the logic of upward-closed sets
    (intuitionistic propositions) does NOT satisfy excluded middle, but DOES satisfy
    the temporal excluded middle R(T(a)) ⊔ R(T(aᶜ)) = ⊤ when composed with the
    frame's accessibility relation.

    Test: Construct a 3-element frame {past, present, future} with access future→past
    and verify computationally that there exists an upward-closed set violating LEM
    but satisfying temporal EM.
-/


