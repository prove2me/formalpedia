-- Prove2me | solution 1 for TropSW.scalar_lattice_density
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:03:18.644842+00:00
-- url     : https://prove2.me/submissions/a25034b6-8bf0-4289-aa49-45a121752745

-- Sol generated from Bridges/StoneWeierstrassTropicalPolytope.lean
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


/-! ### Coordinatewise assembly -/


/-! ### Retraction density bridge -/



/-! ### Vector-valued tropical Stone–Weierstrass -/



/-! ### Finite tropical expression language -/




/-! ### Modulus of continuity -/


/-
Vector modulus from coordinate moduli: if each coordinate of `f` has a monotone
modulus of continuity, then `f` is uniformly continuous with explicit error.
-/


open TropSW in
theorem solution    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : Set (X → ℝ))
    (hA_cont : ∀ f ∈ A, Continuous f)
    (hA_nonempty : A.Nonempty)
    (hA_max : ∀ f g, f ∈ A → g ∈ A → (fun x => max (f x) (g x)) ∈ A)
    (hA_min : ∀ f g, f ∈ A → g ∈ A → (fun x => min (f x) (g x)) ∈ A)
    (hA_sep : TropSeparatesPointsStrongly A) :
    ∀ f : X → ℝ, Continuous f →
    ∀ ε > 0, ∃ g ∈ A, ∀ x, |f x - g x| ≤ ε := by
  set L : Set C(X, ℝ) := {g : C(X, ℝ) | (g : X → ℝ) ∈ A}
  have hL_nonempty : L.Nonempty := by
    obtain ⟨f, hf⟩ := hA_nonempty; exact ⟨⟨f, hA_cont f hf⟩, hf⟩
  have hL_inf : ∀ f ∈ L, ∀ g ∈ L, f ⊓ g ∈ L := by
    intro f hf g hg; show (↑(f ⊓ g) : X → ℝ) ∈ A
    have : (↑(f ⊓ g) : X → ℝ) = fun x => min (f x) (g x) := by
      ext x; simp [ContinuousMap.inf_apply]
    rw [this]; exact hA_min _ _ hf hg
  have hL_sup : ∀ f ∈ L, ∀ g ∈ L, f ⊔ g ∈ L := by
    intro f hf g hg; show (↑(f ⊔ g) : X → ℝ) ∈ A
    have : (↑(f ⊔ g) : X → ℝ) = fun x => max (f x) (g x) := by
      ext x; simp [ContinuousMap.sup_apply]
    rw [this]; exact hA_max _ _ hf hg
  have hL_sep : L.SeparatesPointsStrongly := by
    intro v x y
    obtain ⟨f, hfA, hfx, hfy⟩ := hA_sep v x y
    exact ⟨⟨f, hA_cont f hfA⟩, hfA, hfx, hfy⟩
  have hL_dense : closure L = ⊤ :=
    ContinuousMap.sublattice_closure_eq_top L hL_nonempty hL_inf hL_sup hL_sep
  intro f hf ε hε
  have hf_bun : (⟨f, hf⟩ : C(X, ℝ)) ∈ closure L := by rw [hL_dense]; exact mem_univ _
  rw [Metric.mem_closure_iff] at hf_bun
  obtain ⟨g, hgL, hg_dist⟩ := hf_bun ε hε
  refine ⟨g, hgL, fun x => ?_⟩
  have h2 : dist ((⟨f, hf⟩ : C(X, ℝ)) x) (g x) ≤ dist (⟨f, hf⟩ : C(X, ℝ)) g :=
    ContinuousMap.dist_apply_le_dist x
  simp only [ContinuousMap.coe_mk] at h2
  rw [Real.dist_eq] at h2; linarith
