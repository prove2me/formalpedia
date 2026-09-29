-- Prove2me | Theorems.Thm_ClosureSheafCodeDuality_round_trip_exact_with_gluing
-- name    : ClosureSheafCodeDuality.round_trip_exact_with_gluing
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-16T20:31:03.046971+00:00
-- url     : https://prove2.me/theorems/22f59c34-ae56-4c5f-ab37-4df6f66359ab
-- title:
--   Theorem D (Round-Trip Duality under Gluing):
-- statement:
--   **Theorem D (Round-Trip Duality under Gluing):**
--       Under the finite gluing property, the canonical constraint system of the valid set
--       has the same valid set as the original system. This is the core of the
--       closure-decoder duality: constraint systems with gluing can be fully
--       reconstructed from their valid assignments.
--
--   ```lean
--   theorem ClosureSheafCodeDuality.round_trip_exact_with_gluing(S : ConstraintSystem K Obs)
--       (hne : S.ValidSet.Nonempty) (hglue : S.FiniteGluing) :
--       (canonicalConstraint S.ValidSet hne).ValidSet = S.ValidSet := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ClosureSheafCodeDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ClosureSheafCodeDuality.lean#L290

-- Thm stub generated from Bridges/ClosureSheafCodeDuality.lean
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







/-! ## Section 9: Pairwise Consistency and the Finite Gluing Property

The finite gluing property is the cellular analogue of the sheaf gluing condition.
It states that pairwise consistency (each pair of incident values co-occurs in some
valid assignment) implies global validity. Under this axiom, the round-trip
reconstruction is exact. -/

theorem ClosureSheafCodeDuality.round_trip_exact_with_gluing(S : ConstraintSystem K Obs)
    (hne : S.ValidSet.Nonempty) (hglue : S.FiniteGluing) :
    (canonicalConstraint S.ValidSet hne).ValidSet = S.ValidSet := by sorry
