-- Prove2me | solution 1 for scalar_lattice_density
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:24:01.656278+00:00
-- url     : https://prove2.me/submissions/a3246801-c792-49ce-aa81-60644056bc3c

-- Sol generated from Bridges/PosetTheory/TropicalScalar.lean
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



/-! ### Coordinatewise assembly -/


theorem solution    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : Set (X → ℝ))
    (hA_cont : ∀ f ∈ A, Continuous f)
    (hA_nonempty : A.Nonempty)
    (hA_max : ∀ f g, f ∈ A → g ∈ A → (fun x => max (f x) (g x)) ∈ A)
    (hA_min : ∀ f g, f ∈ A → g ∈ A → (fun x => min (f x) (g x)) ∈ A)
    (hA_sep : TropSeparatesPointsStrongly A) :
    ∀ f : X → ℝ, Continuous f →
    ∀ ε > 0, ∃ g ∈ A, ∀ x, |f x - g x| ≤ ε := by
  -- Step 1: Build the bundled set L ⊆ C(X, ℝ)
  set L := toBundledSet A hA_cont with hL_def
  -- Step 2: Show L is nonempty
  have hL_nonempty : L.Nonempty := by
    obtain ⟨f, hf⟩ := hA_nonempty
    exact ⟨⟨f, hA_cont f hf⟩, hf⟩
  -- Step 3: Show L is closed under inf (= min)
  have hL_inf : ∀ f ∈ L, ∀ g ∈ L, f ⊓ g ∈ L := by
    intro f hf g hg
    show (↑(f ⊓ g) : X → ℝ) ∈ A
    have : (↑(f ⊓ g) : X → ℝ) = fun x => min (f x) (g x) := by
      ext x; simp [ContinuousMap.inf_apply]
    rw [this]
    exact hA_min _ _ hf hg
  -- Step 4: Show L is closed under sup (= max)
  have hL_sup : ∀ f ∈ L, ∀ g ∈ L, f ⊔ g ∈ L := by
    intro f hf g hg
    show (↑(f ⊔ g) : X → ℝ) ∈ A
    have : (↑(f ⊔ g) : X → ℝ) = fun x => max (f x) (g x) := by
      ext x; simp [ContinuousMap.sup_apply]
    rw [this]
    exact hA_max _ _ hf hg
  -- Step 5: Show L separates points strongly
  have hL_sep : L.SeparatesPointsStrongly := by
    intro v x y
    obtain ⟨f, hfA, hfx, hfy⟩ := hA_sep v x y
    exact ⟨⟨f, hA_cont f hfA⟩, hfA, hfx, hfy⟩
  -- Step 6: Apply Mathlib's sublattice_closure_eq_top
  have hL_dense : closure L = ⊤ :=
    ContinuousMap.sublattice_closure_eq_top L hL_nonempty hL_inf hL_sup hL_sep
  -- Step 7: Extract the approximation
  intro f hf ε hε
  have hf_bun : (⟨f, hf⟩ : C(X, ℝ)) ∈ closure L := by
    rw [hL_dense]; exact mem_univ _
  rw [Metric.mem_closure_iff] at hf_bun
  obtain ⟨g, hgL, hg_dist⟩ := hf_bun ε hε
  refine ⟨g, hgL, fun x => ?_⟩
  have h2 : dist ((⟨f, hf⟩ : C(X, ℝ)) x) (g x) ≤ dist (⟨f, hf⟩ : C(X, ℝ)) g :=
    ContinuousMap.dist_apply_le_dist x
  simp only [ContinuousMap.coe_mk] at h2
  rw [Real.dist_eq] at h2
  linarith
