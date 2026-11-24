-- Prove2me | solution 1 for CayleyCensus.walkCount_mulAut
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:38:52.818727+00:00
-- url     : https://prove2.me/submissions/b7cb8339-82ba-4e04-a149-bc9d941a4347

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

theorem solution {S : Finset G} {σ : MulAut G} (h : Preserves σ S)
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

end CayleyCensus

open CayleyCensus

theorem solution {S : Finset G} {σ : MulAut G} (h : Preserves σ S)
    (n : ℕ) (g : G) : walkCount S n (σ g) = walkCount S n g :=
  CayleyCensus.solution h n g

#print axioms solution
