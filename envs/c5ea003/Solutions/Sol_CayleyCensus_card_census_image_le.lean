-- Prove2me | solution 1 for CayleyCensus.card_census_image_le
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:38:52.37492+00:00
-- url     : https://prove2.me/submissions/44d6f52b-752c-4fc1-8d23-6ae0188878c0

import Mathlib
import Definitions.Def_MachineLearning_CayleyCensusInvariance
import Definitions.Def_MachineLearning_CayleyCensusMoments

open CayleyCensus
variable {G : Type*} [Group G]
open CensusEquiv
variable {S : Finset G}
variable [DecidableEq G]
variable [Fintype G]

namespace CayleyCensus

private theorem sum_inv_aux {S : Finset G} (hS : InvClosed S) (f : G → ℕ) :
    ∑ s ∈ S, f s⁻¹ = ∑ s ∈ S, f s :=
  Finset.sum_nbij' (i := fun s => s⁻¹) (j := fun s => s⁻¹)
    (fun _ ha => hS ha) (fun _ ha => hS ha)
    (fun a _ => inv_inv a) (fun a _ => inv_inv a) (fun _ _ => rfl)

private theorem walkCount_inv_aux {S : Finset G} (hS : InvClosed S) (n : ℕ) (g : G) :
    walkCount S n g⁻¹ = walkCount S n g := by
  induction n generalizing g with
  | zero => simp [inv_eq_one]
  | succ n ih =>
      rw [walkCount_succ, walkCount_succ_right]
      have hcongr : ∀ s ∈ S, walkCount S n (s⁻¹ * g⁻¹) = walkCount S n (g * s) := by
        intro s _
        have hrw : s⁻¹ * g⁻¹ = (g * s)⁻¹ := by rw [mul_inv_rev]
        rw [hrw, ih]
      rw [Finset.sum_congr rfl hcongr]
      exact (sum_inv_aux hS (fun s => walkCount S n (g * s))).symm

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

private theorem walkCount_of_censusEquiv_aux {S : Finset G} (hS : InvClosed S) {g h : G}
    (hgh : CensusEquiv S g h) (n : ℕ) : walkCount S n g = walkCount S n h := by
  induction hgh with
  | refl => rfl
  | inv _ ih => rw [walkCount_inv_aux hS, ih]
  | aut σ hσ _ ih => rw [walkCount_mulAut_aux hσ, ih]

private theorem census_of_censusEquiv_aux {S : Finset G} (hS : InvClosed S) {g h : G}
    (hgh : CensusEquiv S g h) : census S g = census S h :=
  funext fun n => walkCount_of_censusEquiv_aux hS hgh n

open scoped Classical in
theorem solution {S : Finset G} (hS : InvClosed S) (T : Finset G)
    (hT : ∀ g : G, ∃ t ∈ T, CensusEquiv S g t) :
    (Finset.univ.image (census S)).card ≤ T.card := by
  have hsub : Finset.univ.image (census S) ⊆ T.image (census S) := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨g, -, rfl⟩
    obtain ⟨t, htT, hgt⟩ := hT g
    exact Finset.mem_image.mpr ⟨t, htT, (census_of_censusEquiv_aux hS hgt).symm⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

end CayleyCensus

open CayleyCensus

open scoped Classical in
theorem solution {S : Finset G} (hS : InvClosed S) (T : Finset G)
    (hT : ∀ g : G, ∃ t ∈ T, CensusEquiv S g t) :
    (Finset.univ.image (census S)).card ≤ T.card :=
  CayleyCensus.solution hS T hT

#print axioms solution
