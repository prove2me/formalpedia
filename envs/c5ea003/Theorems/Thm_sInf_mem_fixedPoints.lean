-- Prove2me | Theorems.Thm_sInf_mem_fixedPoints
-- name    : sInf_mem_fixedPoints
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:35:24.94099+00:00
-- url     : https://prove2.me/theorems/dbee38bb-f938-4ff8-8d87-5cb0b8dacb20
-- title:
--   SInf mem fixedPoints
-- statement:
--   Formal statement of `sInf_mem_fixedPoints` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem sInf_mem_fixedPoints(S : Set α) (hS : S ⊆ retrocausalFixedPoints τ) :
--       retrocausalClosure τ (sInf S) = sInf (retrocausalClosure τ '' S) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PosetTheory/RetrocausalLogic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PosetTheory/RetrocausalLogic.lean#L269

-- Thm stub generated from Bridges/PosetTheory/RetrocausalLogic.lean
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

theorem sInf_mem_fixedPoints(S : Set α) (hS : S ⊆ retrocausalFixedPoints τ) :
    retrocausalClosure τ (sInf S) = sInf (retrocausalClosure τ '' S) := by sorry
