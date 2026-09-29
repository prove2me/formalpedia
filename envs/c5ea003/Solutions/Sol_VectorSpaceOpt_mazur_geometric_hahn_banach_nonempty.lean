-- Prove2me | solution 1 for VectorSpaceOpt.mazur_geometric_hahn_banach_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-06T00:56:03.907903+00:00
-- url     : https://prove2.me/submissions/070a2796-6110-4d6f-9abc-2343f5979ae7

import Mathlib

theorem solution
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (hK : Convex ℝ K) (hKint : (interior K).Nonempty)
    (V : AffineSubspace ℝ X) (hV0 : (V : Set X).Nonempty)
    (hV : ∀ v ∈ V, v ∉ interior K) :
    ∃ (f : X →L[ℝ] ℝ) (c : ℝ),
      f ≠ 0 ∧ (∀ v ∈ V, f v = c) ∧ (∀ k ∈ interior K, f k < c) := by
  obtain ⟨v₀, hv₀⟩ := hV0
  have hdisj : Disjoint (interior K) (V : Set X) := by
    rw [Set.disjoint_left]
    intro a ha haV
    exact hV a haV ha
  obtain ⟨f, u, hf1, hf2⟩ :=
    geometric_hahn_banach_open (hK.interior) isOpen_interior V.convex hdisj
  -- `f` annihilates the direction of `V`
  have hdir : ∀ m ∈ V.direction, f m = 0 := by
    intro m hm
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `f m < 0`: push `t` up
      set t : ℝ := (u - f v₀ - 1) / f m with ht
      have hmem : t • m +ᵥ v₀ ∈ V :=
        AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ t hm) hv₀
      have := hf2 _ hmem
      rw [show (t • m +ᵥ v₀ : X) = t • m + v₀ from rfl] at this
      rw [map_add, map_smul] at this
      simp only [smul_eq_mul] at this
      rw [ht, div_mul_cancel₀ _ (ne_of_lt hlt)] at this
      linarith
    · set t : ℝ := (u - f v₀ - 1) / f m with ht
      have hmem : t • m +ᵥ v₀ ∈ V :=
        AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ t hm) hv₀
      have := hf2 _ hmem
      rw [show (t • m +ᵥ v₀ : X) = t • m + v₀ from rfl] at this
      rw [map_add, map_smul] at this
      simp only [smul_eq_mul] at this
      rw [ht, div_mul_cancel₀ _ (ne_of_gt hgt)] at this
      linarith
  -- hence `f` is constant on `V`
  have hconst : ∀ v ∈ V, f v = f v₀ := by
    intro v hv
    have hm : v -ᵥ v₀ ∈ V.direction := AffineSubspace.vsub_mem_direction hv hv₀
    have := hdir _ hm
    rw [show (v -ᵥ v₀ : X) = v - v₀ from rfl, map_sub] at this
    linarith
  refine ⟨f, f v₀, ?_, hconst, ?_⟩
  · -- `f ≠ 0` because it strictly separates a point of `interior K` from `v₀`
    obtain ⟨a, ha⟩ := hKint
    intro hf0
    have h1 := hf1 a ha
    have h2 := hf2 v₀ hv₀
    rw [hf0] at h1 h2
    simp at h1 h2
    linarith
  · intro k hk
    have h1 := hf1 k hk
    have h2 := hf2 v₀ hv₀
    linarith
