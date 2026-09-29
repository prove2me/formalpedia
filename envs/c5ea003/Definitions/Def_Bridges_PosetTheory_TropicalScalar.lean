-- Prove2me | Definitions.Def_Bridges_PosetTheory_TropicalScalar
-- name    : Bridges_PosetTheory_TropicalScalar
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:51.26667+00:00
-- url     : https://prove2.me/theorems/dec3e9c5-14a4-486b-89bb-bf9aa37f92cb
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_TropicalScalar
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.TropicalScalar`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/TropicalScalar.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Scalar Tropical Stone–Weierstrass Theorem

We prove that a sublattice of continuous scalar functions `X → ℝ` on a compact Hausdorff
space that separates points strongly is uniformly dense, and derive concrete corollaries
for tropical (max-plus) function algebras.

The proof reduces to Mathlib's `ContinuousMap.sublattice_closure_eq_top`.

## Main Results

* `scalar_lattice_density` — Uniform density of a strongly separating sublattice.
* `scalar_tropical_stone_weierstrass` — Same with tropical lattice structure hypotheses.
* `coord_uniform_error_implies_sup_norm_error` — Coordinatewise → sup-norm approximation.
-/

open Set Metric TopologicalSpace Filter ContinuousMap
open scoped Topology

/-! ### Separation predicates -/

/-- Weak separation: some function distinguishes any two distinct points. -/
def TropSeparatesPoints {X : Type*} (A : Set (X → ℝ)) : Prop :=
  ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y

/-- Strong separation: for any two points and any target values, some function
hits both targets. This is the hypothesis for lattice Stone–Weierstrass. -/
def TropSeparatesPointsStrongly {X : Type*} (A : Set (X → ℝ)) : Prop :=
  ∀ (v : X → ℝ) (x y : X), ∃ f ∈ A, f x = v x ∧ f y = v y

/-! ### Tropical lattice structure -/

/-- A "tropical lattice" of functions: contains constants, closed under max, min, shifts. -/
structure IsTropLattice {X : Type*} [TopologicalSpace X]
    (A : Set (X → ℝ)) : Prop where
  /-- Contains all constant functions -/
  const_mem : ∀ c : ℝ, (fun _ : X => c) ∈ A
  /-- Closed under pointwise maximum -/
  max_mem : ∀ f g, f ∈ A → g ∈ A → (fun x => max (f x) (g x)) ∈ A
  /-- Closed under pointwise minimum -/
  min_mem : ∀ f g, f ∈ A → g ∈ A → (fun x => min (f x) (g x)) ∈ A
  /-- Closed under additive shift -/
  shift_mem : ∀ (c : ℝ) f, f ∈ A → (fun x => c + f x) ∈ A

/-! ### The bundled set of ContinuousMaps -/

/-- Bundle a set of continuous unbundled functions into a set of `ContinuousMap`s. -/
def toBundledSet {X : Type*} [TopologicalSpace X]
    (A : Set (X → ℝ)) (_hA_cont : ∀ f ∈ A, Continuous f) : Set C(X, ℝ) :=
  {g : C(X, ℝ) | (g : X → ℝ) ∈ A}

/-! ### Main scalar density theorem -/



/-! ### Coordinatewise assembly -/


