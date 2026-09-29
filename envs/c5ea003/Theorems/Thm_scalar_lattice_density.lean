-- Prove2me | Theorems.Thm_scalar_lattice_density
-- name    : scalar_lattice_density
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:35:29.124887+00:00
-- url     : https://prove2.me/theorems/25a66b80-8728-4856-9249-2e67d70df58e
-- title:
--   Scalar Lattice Density Theorem: A nonempty set of continuous functions on a
-- statement:
--   **Scalar Lattice Density Theorem**: A nonempty set of continuous functions on a
--   compact Hausdorff space, closed under max and min and separating points strongly,
--   is uniformly dense. For any continuous `f` and `ε > 0`, there exists `g ∈ A` with
--   `|f(x) - g(x)| ≤ ε` for all `x`.
--
--   ```lean
--   theorem scalar_lattice_density    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
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
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PosetTheory/TropicalScalar.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PosetTheory/TropicalScalar.lean#L59

-- Thm stub generated from Bridges/PosetTheory/TropicalScalar.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_TropicalScalar
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



/-! ### Tropical lattice structure -/


/-! ### The bundled set of ContinuousMaps -/


/-! ### Main scalar density theorem -/

theorem scalar_lattice_density    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : Set (X → ℝ))
    (hA_cont : ∀ f ∈ A, Continuous f)
    (hA_nonempty : A.Nonempty)
    (hA_max : ∀ f g, f ∈ A → g ∈ A → (fun x => max (f x) (g x)) ∈ A)
    (hA_min : ∀ f g, f ∈ A → g ∈ A → (fun x => min (f x) (g x)) ∈ A)
    (hA_sep : TropSeparatesPointsStrongly A) :
    ∀ f : X → ℝ, Continuous f →
    ∀ ε > 0, ∃ g ∈ A, ∀ x, |f x - g x| ≤ ε := by sorry
