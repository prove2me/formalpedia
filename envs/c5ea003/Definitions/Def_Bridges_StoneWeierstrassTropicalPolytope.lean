-- Prove2me | Definitions.Def_Bridges_StoneWeierstrassTropicalPolytope
-- name    : Bridges_StoneWeierstrassTropicalPolytope
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:09.78934+00:00
-- url     : https://prove2.me/theorems/7c537e80-4450-47e6-a525-11cce9eaefdb
-- title:
--   Aether Catalog definitions — Bridges_StoneWeierstrassTropicalPolytope
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.StoneWeierstrassTropicalPolytope`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/StoneWeierstrassTropicalPolytope.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Stone–Weierstrass for Compact Polytope Codomains

This file proves the full **coordinatewise tropical Stone–Weierstrass theorem**:
any continuous map from a compact Hausdorff space into a finite-dimensional tropical
space `Fin n → ℝ` can be uniformly approximated by elements from a tropical lattice
of functions.

## Main Results

* `TropSW.scalar_lattice_density` — Scalar lattice density (the core lemma).
* `TropSW.tropical_stone_weierstrass_fin` — Vector-valued density theorem.
* `TropSW.tropical_stone_weierstrass_into_polytope` — With retraction into `K`.
* `TropSW.dense_under_continuous_retraction` — Retraction-preserves-density bridge.
* `TropSW.coord_sup_norm_bound` — Coordinatewise → sup-norm assembly.

## Architecture

The proof proceeds by:
1. Reducing to Mathlib's `ContinuousMap.sublattice_closure_eq_top`.
2. Assembling coordinatewise approximants via the sup-norm bound.
3. Optionally composing with a continuous retraction.
-/

open Set Metric TopologicalSpace Filter ContinuousMap
open scoped BigOperators Topology

namespace TropSW

/-! ### Tropical types and operations -/

/-- Tropical n-dimensional vectors. -/
abbrev Trop (n : ℕ) := Fin n → ℝ




/-! ### Separation predicates -/


/-- Strong separation: for any two points and target values, some function hits both. -/
def TropSeparatesPointsStrongly {X : Type*} (A : Set (X → ℝ)) : Prop :=
  ∀ (v : X → ℝ) (x y : X), ∃ f ∈ A, f x = v x ∧ f y = v y

/-! ### Tropical lattice structure -/


/-! ### Core scalar density theorem -/


/-! ### Coordinatewise assembly -/


/-! ### Retraction density bridge -/



/-! ### Vector-valued tropical Stone–Weierstrass -/



/-! ### Finite tropical expression language -/




/-! ### Modulus of continuity -/

/-- A monotone modulus of continuity for `u`: `ω` is monotone, bounds the oscillation
of `u`, and vanishes at the origin. -/
def IsModulusOfContinuity {X : Type*} [PseudoMetricSpace X]
    (u : X → ℝ) (ω : ℝ → ℝ) : Prop :=
  Monotone ω ∧
  (∀ ε > 0, ∃ δ > 0, ω δ ≤ ε) ∧
  (∀ x y, |u x - u y| ≤ ω (dist x y))

/-
Vector modulus from coordinate moduli: if each coordinate of `f` has a monotone
modulus of continuity, then `f` is uniformly continuous with explicit error.
-/

end TropSW


