-- Prove2me | solution 1 for sInf_mem_fixedPoints
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:22:30.142562+00:00
-- url     : https://prove2.me/submissions/1c861ebe-d4f8-4df6-92c6-860143d6a43b

-- Sol generated from Bridges/PosetTheory/RetrocausalLogic.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_RetrocausalLogic
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


open TemporalGaloisConnection

variable {α : Type*} [Preorder α] (τ : TemporalGaloisConnection α)

/-- Forward propagation is monotone (a consequence of the Galois connection). -/
theorem T_monotone : Monotone τ.T := τ.gc.monotone_l

/-- Backward propagation is monotone. -/
theorem R_monotone : Monotone τ.R := τ.gc.monotone_u




/-! ## Retrocausal Closure Operator -/




variable {α : Type*} [PartialOrder α] (τ : TemporalGaloisConnection α)



/-
The retrocausal closure is idempotent: R(T(R(T(a)))) = R(T(a)).
    This is a key property showing that the closure stabilizes after one application.
    The proof uses the Galois connection adjunction essentially.
-/


/-
The retrocausal interior is idempotent: T(R(T(R(a)))) = T(R(a)).
-/


/-! ## Lattice Properties of Temporal Operators -/


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


/-! ## Temporal Excluded Middle -/


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


/-! ## CPT Symmetry -/


open CPTTriple

variable {α : Type*} (cpt : CPTTriple α)


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


/-! ## Retrocausal Fixed Points -/



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


/-! ## Retrocausal Monad Structure -/


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


/-! ## Intuitionistic Character of Retrocausal Logic -/


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

-- open removed: section is not a namespace
namespace TemporalGaloisConnection
/-- Backward propagation is monotone. -/
theorem R_monotone : Monotone τ.R := τ.gc.monotone_u

end TemporalGaloisConnection

namespace TemporalGaloisConnection
/-- Forward propagation is monotone (a consequence of the Galois connection). -/
theorem T_monotone : Monotone τ.T := τ.gc.monotone_l

end TemporalGaloisConnection

theorem solution(S : Set α) (hS : S ⊆ retrocausalFixedPoints τ) :
    retrocausalClosure τ (sInf S) = sInf (retrocausalClosure τ '' S) := by
  -- Since each s ∈ S is a fixed point, R(T(s)) = s. So the RHS ⨅ (R∘T '' S) = ⨅ S.
  have h_rhs : sInf (retrocausalClosure τ '' S) = sInf S := by
    rw [ Set.image_congr ( fun x hx => by rw [ Set.mem_setOf.mp ( hS hx ) ] ), Set.image_id' ];
  -- Since R is monotone, R(⨅ S) ≤ ⨅ (R '' S).
  have hR_mono : τ.R (sInf (τ.T '' S)) ≤ sInf (τ.R '' (τ.T '' S)) := by
    exact le_sInf fun x hx => by rcases hx with ⟨ y, hy, rfl ⟩ ; exact τ.R_monotone ( sInf_le hy ) ;
  refine' le_antisymm _ _;
  · refine' le_trans _ ( hR_mono.trans _ );
    · exact τ.R_monotone ( show τ.T ( sInf S ) ≤ sInf ( τ.T '' S ) from by exact le_sInf fun x hx => by rcases hx with ⟨ y, hy, rfl ⟩ ; exact τ.T_monotone ( sInf_le hy ) );
    · simp +decide [ retrocausalClosure, Set.image_image ];
  · exact τ.gc.le_iff_le.1 ( by aesop )
