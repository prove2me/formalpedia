-- Prove2me | Theorems.Thm_TropSW_scalar_lattice_density
-- name    : TropSW.scalar_lattice_density
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:19:29.604788+00:00
-- url     : https://prove2.me/theorems/5e539a88-610d-4c8f-8daa-14c25ed91c55
-- title:
--   Scalar Lattice Density: A nonempty set of continuous functions on a compact
-- statement:
--   **Scalar Lattice Density**: A nonempty set of continuous functions on a compact
--   Hausdorff space, closed under max and min and separating points strongly, is
--   uniformly dense.
--
--   ```lean
--   theorem TropSW.scalar_lattice_density    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
--       (A : Set (X → ℝ))
--       (hA_cont : ∀ f ∈ A, Continuous f)
--       (hA_nonempty : A.Nonempty)
--       (hA_max : ∀ f g, f ∈ A → g ∈ A → (fun x => max (f x) (g x)) ∈ A)
--       (hA_min : ∀ f g, f ∈ A → g ∈ A → (fun x => min (f x) (g x)) ∈ A)
--       (hA_sep : TropSeparatesPointsStrongly A) :
--       ∀ f : X → ℝ, Continuous f →
--       ∀ ε > 0, ∃ g ∈ A, ∀ x, |f x - g x| ≤ ε := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/StoneWeierstrassTropicalPolytope.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/StoneWeierstrassTropicalPolytope.lean#L72

-- Thm stub generated from Bridges/StoneWeierstrassTropicalPolytope.lean
import Mathlib
import Definitions.Def_Bridges_StoneWeierstrassTropicalPolytope
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

open TropSW

/-! ### Tropical types and operations -/





/-! ### Separation predicates -/



/-! ### Tropical lattice structure -/


/-! ### Core scalar density theorem -/

theorem TropSW.scalar_lattice_density    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : Set (X → ℝ))
    (hA_cont : ∀ f ∈ A, Continuous f)
    (hA_nonempty : A.Nonempty)
    (hA_max : ∀ f g, f ∈ A → g ∈ A → (fun x => max (f x) (g x)) ∈ A)
    (hA_min : ∀ f g, f ∈ A → g ∈ A → (fun x => min (f x) (g x)) ∈ A)
    (hA_sep : TropSeparatesPointsStrongly A) :
    ∀ f : X → ℝ, Continuous f →
    ∀ ε > 0, ∃ g ∈ A, ∀ x, |f x - g x| ≤ ε := by sorry
