-- Prove2me | Definitions.Def_Bridges_LawvereThermodynamicGalois
-- name    : Bridges_LawvereThermodynamicGalois
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:46.448527+00:00
-- url     : https://prove2.me/theorems/61307f9e-de40-45d0-9827-ea8b609b4c6a
-- title:
--   Aether Catalog definitions — Bridges_LawvereThermodynamicGalois
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.LawvereThermodynamicGalois`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/LawvereThermodynamicGalois.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Lawvere–Thermodynamic Galois Correspondence

## Overview

This file formalizes the **Lawvere–Thermodynamic Galois Correspondence**, which
identifies derivability closure in proof theory with the closure operator
induced by a thermodynamic adjunction between proof states and observables.

The key insight is that given:
- A preorder `P` of proof states,
- A preorder `O` of thermodynamic observables,
- An antitone "lower-envelope" map `lowerEnv : P → O`,
- An antitone "theory-of" map `theoryOf : O → P`,

satisfying the adjunction law `lowerEnv p ≤ o ↔ p ≤ theoryOf o`
(with appropriate dualization), the composite `theoryOf ∘ lowerEnv` is a
closure operator on `P` whose fixed points are exactly `Set.range theoryOf`.

This means: **derivability-closed proof states are exactly those cut out by
thermodynamic observables.**

## Main results

- `ThermoGaloisContext'` — the abstract interface for the adjunction
- `thermoClosure` — the induced closure operator `theoryOf ∘ lowerEnv`
- `thermoClosureOperator` — packaging as Mathlib's `ClosureOperator`
- `fixedPoints_thermoClosure_eq_range_theoryOf` — the representation theorem
- `refineIter_eventually_stable` — finite stabilization of iterative refinement
- `refineIter_stabilizes_by_card` — cardinality-bounded convergence
- `refineIter_limit_is_closed` — the limit is a fixed point of closure

## References

- F. W. Lawvere, *Metric spaces, generalized logic, and closed categories*, 1973
- The thermodynamic interpretation follows the analogy between free-energy
  profiles and semantic separation in proof theory.
-/

open OrderDual Set

universe u v

/-! ## The Thermodynamic Galois Context -/

/-- A `ThermoGaloisContext'` packages a Galois connection between proof states `P`
and dualized observables `OrderDual O`. The map `lowerEnv` sends a proof state
to its free-energy profile (in `OrderDual O`), and `theoryOf` sends an observable
to the derivability-closed theory it determines. The Galois connection axiom
encodes: `lowerEnv p ≤ o ↔ p ≤ theoryOf o` (with `o : OrderDual O`). -/
structure ThermoGaloisContext' (P : Type u) (O : Type v) [Preorder P] [Preorder O] where
  /-- The lower-envelope / free-energy profile map from proof states to dualized observables. -/
  lowerEnv : P → OrderDual O
  /-- The theory map from dualized observables to proof states. -/
  theoryOf : OrderDual O → P
  /-- The Galois connection between `lowerEnv` and `theoryOf`. -/
  gc : GaloisConnection lowerEnv theoryOf

/-! ## The Thermodynamic Closure Operator -/

/-- The thermodynamic closure of a proof state: apply the lower-envelope map
and then recover the theory. This is the composite `theoryOf ∘ lowerEnv`. -/
def thermoClosure {P : Type u} {O : Type v} [Preorder P] [Preorder O]
    (h : ThermoGaloisContext' P O) : P → P :=
  fun p => h.theoryOf (h.lowerEnv p)






/-! ## Packaging as a Mathlib ClosureOperator -/

/-- The thermodynamic closure packaged as a Mathlib `ClosureOperator`. -/
noncomputable def thermoClosureOperator {P : Type u} {O : Type v}
    [PartialOrder P] [Preorder O]
    (h : ThermoGaloisContext' P O) : ClosureOperator P :=
  h.gc.closureOperator


/-! ## Fixed-Point Characterization -/





/-
If a derivability closure has the same fixed points as `thermoClosure`,
then they agree pointwise.
-/

/-
A Galois connection induces a closure operator with the expected properties.
-/

/-
The fixed-point/range theorem for an abstract Galois connection.
-/

/-! ## Iterative Refinement and Finite Stabilization -/

/-- One step of the alternating refinement: apply `theoryOf ∘ lowerEnv`. -/
def refineStep {P : Type u} {O : Type v} [Preorder P] [Preorder O]
    (h : ThermoGaloisContext' P O) : P → P :=
  thermoClosure h

/-- Iterated refinement starting from a proof state. -/
def refineIter {P : Type u} {O : Type v} [Preorder P] [Preorder O]
    (h : ThermoGaloisContext' P O) : ℕ → P → P
  | 0, p => p
  | n + 1, p => refineStep h (refineIter h n p)

/-
Each refinement step is at least as large as the previous one.
-/

/-
The refinement iteration stabilizes after just 1 step, since
`thermoClosure` is idempotent.
-/

/-
On a finite partial order, iterative refinement eventually stabilizes.
-/

/-
On a finite partial order, refinement stabilizes by `Fintype.card P` steps.
In fact, it stabilizes after 1 step by idempotency.
-/

/-
The stabilized value is closed under thermodynamic closure.
-/


