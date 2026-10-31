-- Prove2me | solution 1 for KServer.chunk_potential_iff
-- status  : ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T06:16:45.757423+00:00
-- url     : https://prove2.me/submissions/3a7d0be6-2c5d-44e1-9e46-618a29c35cd1

import Definitions.Def_KServer_chunk_potentials

open KServer

theorem solution {X : Type*} [MetricSpace X] [Fintype X]
    {Ω : Type*} [Fintype Ω] (p : ℝ) (n : ℕ) (P : Ω → ℝ)
    (σ : Ω → List (Set X)) (v : X → ℝ) :
    IsChunkPotential p n P σ v ↔ ∀ x, v x ≤ chunkBellman p n P σ x := by
  classical
  induction n generalizing P σ v with
  | zero => rfl
  | succ n ih =>
    constructor
    · rintro ⟨z, u, hu, hescape, hcontinue, hempty, hmove⟩ x
      change v x ≤ min _ _
      apply le_min (hescape x)
      refine (hcontinue x).trans ?_
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : S.Nonempty
      · rw [dif_pos hS]
        apply Finset.le_inf'
        intro y hy
        have hym : y ∈ S := by simpa using hy
        have hchild := (ih _ _ (u S)).mp (hu S) y
        exact (hmove S hS x y hym).trans (add_le_add le_rfl hchild)
      · rw [dif_neg hS]
        exact hempty S hS x
    · intro hv
      let u : Set X → X → ℝ := fun S y => chunkBellman p n
        (fun ω => if (σ ω).head? = some S then P ω else 0)
        (fun ω => (σ ω).tail) y
      let z : Set X → X → ℝ := fun S x => if hS : S.Nonempty then
        (Finset.univ.filter (fun y : X => y ∈ S)).inf'
          (by obtain ⟨y, hy⟩ := hS; exact ⟨y, by simp [hy]⟩)
          (fun y => (∑ ω, if (σ ω).head? = some S then P ω else 0) * dist x y + u S y)
        else 0
      refine ⟨z, u, ?_, ?_, ?_, ?_, ?_⟩
      · intro S
        exact (ih _ _ (u S)).mpr (fun y => le_rfl)
      · intro x
        exact (hv x).trans (min_le_left _ _)
      · intro x
        exact (hv x).trans (min_le_right _ _)
      · intro S hS x
        simp [z, hS]
      · intro S hS x y hy
        dsimp [z]
        rw [dif_pos hS]
        exact Finset.inf'_le _ (by simp [hy])
