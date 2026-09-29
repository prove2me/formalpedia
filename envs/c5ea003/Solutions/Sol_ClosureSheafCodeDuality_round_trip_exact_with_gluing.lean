-- Prove2me | solution 1 for ClosureSheafCodeDuality.round_trip_exact_with_gluing
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-16T21:18:08.051033+00:00
-- url     : https://prove2.me/submissions/741cb86f-29ff-4590-9430-af5de9a87fb7

-- Sol generated from Bridges/ClosureSheafCodeDuality.lean
import Mathlib
import Definitions.Def_Bridges_ClosureSheafCodeDuality
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Closure-Sheaf Code Duality via Cellular Decoder Reconstruction

## Overview

We establish a finite duality between constraint-closure systems on finite cell complexes
and cellular decoder presentations. The main results are:

1. **Reconstruction (Theorem A)**: Every constraint system yields a canonical decoder
   whose codewords are exactly the valid (zero-defect) assignments.
2. **Inverse Reconstruction (Theorem B)**: Every decoder yields a canonical constraint
   system whose valid set contains the original codewords.
3. **Minimality (Theorem C)**: The canonical constraint system induced by a set of
   assignments has the smallest domains among all systems accepting those assignments.
   This is the cellular Myhill–Nerode theorem.
4. **Round-Trip Duality (Theorem D)**: Under a finite gluing axiom, the round-trip
   closure → decoder → closure recovers the original valid set exactly.
5. **Certified Decoder (Theorem E)**: The canonical decoder construction is sound,
   complete, and produces minimal domains via refinement.

## Mathematical Context

This formalizes the "closure-decoder duality": constraint propagation systems (modeling
local physics, CSP, or coding constraints) are equivalent to local decoder presentations.
The defect functional measures failure of local consistency, and minimization via a kernel
congruence gives a cellular Myhill–Nerode theorem. The finite gluing axiom bridges
pairwise local consistency to global codeword reconstruction.
-/

open Set Function Finset Classical

noncomputable section

open ClosureSheafCodeDuality

/-! ## Section 1: Finite Cell Complexes -/


attribute [instance] CellComplex.cellFintype CellComplex.cellDecEq CellComplex.incDecRel

open CellComplex

variable (K : CellComplex)





/-! ## Section 2: Constraint Systems -/

variable {K : CellComplex} {Obs : Type*} [Fintype Obs] [DecidableEq Obs]





/-! ## Section 3: Cellular Decoders -/





/-! ## Section 4: Defect Functional -/






/-! ## Section 5: Closure Operators -/





/-! ## Section 6: Closure-Cosheaf Systems -/


/-! ## Section 7: Canonical Constructions

The canonical decoder from a constraint system checks domain membership and compatibility.
The canonical constraint system from a set of assignments uses projections as domains
and co-occurrence as compatibility. These are the two directions of the duality. -/



/-! ## Section 8: Core Duality Theorems -/




/-- **Theorem B (Decoder-to-Closure Canonicalization):**
    The canonical constraint system induced by a set of assignments W
    has valid set containing W. -/
theorem canonical_constraint_contains (W : Set (Assignment K Obs))
    (hne : W.Nonempty) :
    W ⊆ (canonicalConstraint W hne).ValidSet := by
  intro f hf
  refine ⟨fun σ => ?_, fun σ τ _ => ?_⟩
  · simp only [canonicalConstraint, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨f, hf, rfl⟩
  · exact ⟨f, hf, rfl, rfl⟩



/-! ## Section 9: Pairwise Consistency and the Finite Gluing Property

The finite gluing property is the cellular analogue of the sheaf gluing condition.
It states that pairwise consistency (each pair of incident values co-occurs in some
valid assignment) implies global validity. Under this axiom, the round-trip
reconstruction is exact. -/





/-! ## Section 10: Extensibility and Domain Recovery -/



/-! ## Section 11: Kernel Congruence (Cellular Myhill–Nerode)

The zero-defect kernel congruence identifies observables that behave identically
in all valid assignments. The quotient by this congruence gives the minimal
state space — the cellular analogue of the Myhill–Nerode theorem for automata. -/







/-! ## Section 12: Codeword Equivalence -/




/-! ## Section 13: Certified Decoder -/



/-! ## Section 14: Zero-Defect Sections Equal Codewords -/




/-! ## Section 15: Refinement to Reachable States

The refinement operator projects a constraint system down to its reachable states:
domain values that actually appear in valid assignments. This is the algorithmic
core of the Myhill–Nerode minimization. -/







/-! ## Section 16: Main Duality Theorem -/



/-! ## Section 17: Defect Preservation -/



/-! ## Section 18: Concrete Example — Path Graph Repetition Code -/








open ClosureSheafCodeDuality in
theorem solution(S : ConstraintSystem K Obs)
    (hne : S.ValidSet.Nonempty) (hglue : S.FiniteGluing) :
    (canonicalConstraint S.ValidSet hne).ValidSet = S.ValidSet := by
  ext f
  constructor
  · intro hf
    apply hglue
    constructor
    · intro σ
      have hdom := hf.1 σ
      simp only [canonicalConstraint, Finset.mem_filter, Finset.mem_univ, true_and] at hdom
      exact hdom
    · intro σ τ hinc
      exact hf.2 σ τ hinc
  · intro hf; exact canonical_constraint_contains S.ValidSet hne hf
