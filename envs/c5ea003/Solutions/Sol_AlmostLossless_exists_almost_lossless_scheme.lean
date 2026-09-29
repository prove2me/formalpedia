-- Prove2me | solution 1 for AlmostLossless.exists_almost_lossless_scheme
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T10:12:41.615665+00:00
-- url     : https://prove2.me/submissions/9ce7dd7d-3c2a-4f54-b80b-de7514d57666

import Mathlib
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Theorems.Thm_AlmostLossless_exists_good_key
import Theorems.Thm_AlmostLossless_collides_iff
import Theorems.Thm_AlmostLossless_setMass_univ
import Theorems.Thm_AlmostLossless_setMass_mono
import Theorems.Thm_AlmostLossless_setMass_union_le
import Theorems.Thm_AlmostLossless_hashScheme_succeeds
import Theorems.Thm_AlmostLossless_silentError_imp_collides
import Theorems.Thm_AlmostLossless_scanCost_snd

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Finset BigOperators NonArchInfoTheory AlmostLossless
variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}

theorem solution (μ : FinProbDist α) {H : Fin K → α → Fin M}
    (hU : Universal2 H) (hK : 0 < K) (hM : 0 < M)
    (l : List α) (hnd : l.Nodup) (δ : ℝ) (hδ : setMass μ (l.toFinset)ᶜ ≤ δ) :
    ∃ k : Fin K,
      setMass μ (Finset.univ.filter (fun x => ¬ (hashScheme l (H k)).Succeeds x))
          ≤ δ + (l.length : ℝ) / M
      ∧ setMass μ (Finset.univ.filter (fun x => (hashScheme l (H k)).SilentError x))
          ≤ (l.length : ℝ) / M
      ∧ ∀ i : Fin M, (scanCost (H k) i l).2 = l.length := by
  classical
  obtain ⟨k, hk⟩ := exists_good_key μ hU hK l.toFinset Finset.univ
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hcard : (l.toFinset.card : ℝ) = (l.length : ℝ) := by
    rw [List.toFinset_card_of_nodup hnd]
  -- the collision mass of the chosen key
  set C : Finset α := Finset.univ.filter (fun x => Collides H k l.toFinset x) with hC
  have hCbound : setMass μ C ≤ (l.length : ℝ) / M := by
    rw [le_div_iff₀ hMR]
    have h2 := hk
    rw [setMass_univ, mul_one, hcard] at h2
    linarith [h2, mul_comm (M : ℝ) (setMass μ C)]
  refine ⟨k, ?_, ?_, fun i => scanCost_snd _ _ _⟩
  · -- failure ⊆ (codebook)ᶜ ∪ collisions
    have hsub : Finset.univ.filter (fun x => ¬ (hashScheme l (H k)).Succeeds x)
        ⊆ (l.toFinset)ᶜ ∪ C := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Finset.mem_union]
      by_cases hxl : x ∈ l.toFinset
      · right
        rw [hC, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [collides_iff]
        by_contra hnc
        exact hx (hashScheme_succeeds hnd (List.mem_toFinset.mp hxl) hnc)
      · left; exact Finset.mem_compl.mpr hxl
    calc setMass μ (Finset.univ.filter (fun x => ¬ (hashScheme l (H k)).Succeeds x))
        ≤ setMass μ ((l.toFinset)ᶜ ∪ C) := setMass_mono μ hsub
      _ ≤ setMass μ (l.toFinset)ᶜ + setMass μ C := setMass_union_le μ _ _
      _ ≤ δ + (l.length : ℝ) / M := add_le_add hδ hCbound
  · have hsub : Finset.univ.filter (fun x => (hashScheme l (H k)).SilentError x) ⊆ C := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [hC, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, collides_iff.mpr (silentError_imp_collides hx)⟩
    exact le_trans (setMass_mono μ hsub) hCbound


#print axioms solution
