-- Prove2me | solution 1 for CayleyCensus.walkCount_conj
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:38:50.796324+00:00
-- url     : https://prove2.me/submissions/17f80cd3-8169-438c-b1a7-2b5f5fcaa032

import Mathlib
import Definitions.Def_MachineLearning_CayleyCensusInvariance
import Definitions.Def_MachineLearning_CayleyCensusMoments

open CayleyCensus
variable {G : Type*} [Group G]
open CensusEquiv
variable {S : Finset G}
variable [DecidableEq G]

namespace CayleyCensus

private theorem preserves_inv_aux {σ : MulAut G} {S : Finset G} (h : Preserves σ S) :
    Preserves σ⁻¹ S := by
  intro s
  have h1 := h (σ⁻¹ s)
  simpa using h1.symm

private theorem preserves_sum_comp_aux {σ : MulAut G} {S : Finset G} (h : Preserves σ S)
    (f : G → ℕ) : ∑ s ∈ S, f (σ s) = ∑ s ∈ S, f s :=
  Finset.sum_nbij' (i := fun s => σ s) (j := fun s => σ⁻¹ s)
    (fun a ha => (h a).mpr ha)
    (fun a ha => (preserves_inv_aux h a).mpr ha)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => rfl)

private theorem walkCount_mulAut_aux {S : Finset G} {σ : MulAut G} (h : Preserves σ S)
    (n : ℕ) (g : G) : walkCount S n (σ g) = walkCount S n g := by
  induction n generalizing g with
  | zero =>
      simp only [walkCount_zero]
      congr 1
      simp [map_eq_one_iff σ σ.injective]
  | succ n ih =>
      rw [walkCount_succ, walkCount_succ]
      rw [← preserves_sum_comp_aux h (fun s => walkCount S n (s⁻¹ * σ g))]
      refine Finset.sum_congr rfl fun s _ => ?_
      have hrw : (σ s)⁻¹ * σ g = σ (s⁻¹ * g) := by simp
      rw [hrw, ih]

theorem solution {S : Finset G}
    (hS : ∀ (a : G) ⦃s : G⦄, s ∈ S → a * s * a⁻¹ ∈ S)
    (n : ℕ) (a g : G) : walkCount S n (a * g * a⁻¹) = walkCount S n g := by
  have h : Preserves (MulAut.conj a) S := by
    intro s
    constructor
    · intro hs
      have h2 := hS a⁻¹ hs
      simpa [MulAut.conj, mul_assoc] using h2
    · intro hs
      simpa [MulAut.conj] using hS a hs
  simpa [MulAut.conj] using walkCount_mulAut_aux h n g

end CayleyCensus

open CayleyCensus

theorem solution {S : Finset G}
    (hS : ∀ (a : G) ⦃s : G⦄, s ∈ S → a * s * a⁻¹ ∈ S)
    (n : ℕ) (a g : G) : walkCount S n (a * g * a⁻¹) = walkCount S n g :=
  CayleyCensus.solution hS n a g

#print axioms solution
