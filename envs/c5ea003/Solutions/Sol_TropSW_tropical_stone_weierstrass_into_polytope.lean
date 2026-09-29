-- Prove2me | solution 1 for TropSW.tropical_stone_weierstrass_into_polytope
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:04:57.057963+00:00
-- url     : https://prove2.me/submissions/7c34e51b-c01d-4f8e-87e8-ba666b713277

-- Sol generated from Bridges/StoneWeierstrassTropicalPolytope.lean
import Mathlib
import Definitions.Def_Bridges_StoneWeierstrassTropicalPolytope
import Theorems.Thm_TropSW_scalar_lattice_density
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

/-- Coordinatewise approximation implies sup-norm approximation for `Fin n → ℝ`. -/
theorem coord_sup_norm_bound
    {X : Type*} {n : ℕ} (f g : X → Fin n → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ (i : Fin n) (x : X), |f x i - g x i| ≤ ε) :
    ∀ x : X, ‖f x - g x‖ ≤ ε := by
  intro x; rw [pi_norm_le_iff_of_nonneg hε]
  intro i; rw [Real.norm_eq_abs]; exact h i x

/-! ### Retraction density bridge -/


/-- Retraction ensures codomain correctness. -/
theorem retraction_maps_into {X Y : Type*} (K : Set Y) (r : Y → Y)
    (hr_maps : MapsTo r univ K) (g : X → Y) : MapsTo (r ∘ g) univ K :=
  fun _ _ => hr_maps (mem_univ _)

/-! ### Vector-valued tropical Stone–Weierstrass -/

/-- **Tropical Stone–Weierstrass (finite-dimensional version)**: Given a tropical
lattice of continuous functions that separates points strongly, any continuous
`f : X → Fin n → ℝ` is uniformly approximable coordinatewise. -/
theorem tropical_stone_weierstrass_fin
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {n : ℕ}
    (A : Set (X → ℝ))
    (hA_cont : ∀ f ∈ A, Continuous f)
    (hA_nonempty : A.Nonempty)
    (hA_max : ∀ f g, f ∈ A → g ∈ A → (fun x => max (f x) (g x)) ∈ A)
    (hA_min : ∀ f g, f ∈ A → g ∈ A → (fun x => min (f x) (g x)) ∈ A)
    (hA_sep : TropSeparatesPointsStrongly A)
    (f : X → Trop n)
    (hf_cont : Continuous f) :
    ∀ ε > 0, ∃ (g : X → Trop n), (∀ (i : Fin n), (fun x => g x i) ∈ A) ∧
      ∀ x : X, ‖f x - g x‖ ≤ ε := by
  intro ε hε
  have h_coord : ∀ i : Fin n, ∃ gi ∈ A, ∀ x, |f x i - gi x| ≤ ε := by
    intro i
    exact scalar_lattice_density A hA_cont hA_nonempty hA_max hA_min hA_sep
      (fun x => f x i) (continuous_pi_iff.mp hf_cont i) ε hε
  choose gi hgi_mem hgi_close using h_coord
  exact ⟨fun x i => gi i x, fun i => hgi_mem i,
    fun x => coord_sup_norm_bound f (fun x i => gi i x) ε (le_of_lt hε)
      (fun i x => hgi_close i x) x⟩


/-! ### Finite tropical expression language -/




/-! ### Modulus of continuity -/


/-
Vector modulus from coordinate moduli: if each coordinate of `f` has a monotone
modulus of continuity, then `f` is uniformly continuous with explicit error.
-/


open TropSW in
theorem solution    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {n : ℕ}
    (K : Set (Trop n))
    (r : Trop n → Trop n)
    (hr_unif : UniformContinuous r)
    (hr_retract : ∀ x ∈ K, r x = x)
    (hr_maps : MapsTo r univ K)
    (A : Set (X → ℝ))
    (hA_cont : ∀ f ∈ A, Continuous f)
    (hA_nonempty : A.Nonempty)
    (hA_max : ∀ f g, f ∈ A → g ∈ A → (fun x => max (f x) (g x)) ∈ A)
    (hA_min : ∀ f g, f ∈ A → g ∈ A → (fun x => min (f x) (g x)) ∈ A)
    (hA_sep : TropSeparatesPointsStrongly A)
    (f : X → Trop n)
    (hf_cont : Continuous f)
    (hf_maps : MapsTo f univ K) :
    ∀ ε > 0, ∃ (g : X → Trop n), MapsTo g univ K ∧
      ∀ x : X, dist (f x) (g x) ≤ ε := by
  intro ε hε
  rw [Metric.uniformContinuous_iff] at hr_unif
  obtain ⟨δ, hδ_pos, hδ⟩ := hr_unif ε hε
  obtain ⟨g₀, _, hg₀_close⟩ :=
    tropical_stone_weierstrass_fin A hA_cont hA_nonempty hA_max hA_min hA_sep
      f hf_cont (δ / 2) (by linarith)
  refine ⟨r ∘ g₀, retraction_maps_into K r hr_maps g₀, fun x => ?_⟩
  have hfx : r (f x) = f x := hr_retract (f x) (hf_maps (mem_univ x))
  rw [← hfx]
  apply le_of_lt
  apply hδ
  calc dist (f x) (g₀ x) = ‖f x - g₀ x‖ := by rw [dist_eq_norm]
    _ ≤ δ / 2 := hg₀_close x
    _ < δ := by linarith
