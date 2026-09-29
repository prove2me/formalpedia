-- Prove2me | solution 1 for AlmostLossless.exists_list_scheme_indepT
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T10:12:42.595535+00:00
-- url     : https://prove2.me/submissions/43d9a6e2-8b3e-47cd-b1f6-d53145d78f04

import Mathlib
import Definitions.Def_Bridges_AlmostLosslessTwiseIndependent
import Theorems.Thm_AlmostLossless_exists_good_key_indepT
import Theorems.Thm_AlmostLossless_setMass_univ
import Theorems.Thm_AlmostLossless_setMass_mono
import Theorems.Thm_AlmostLossless_setMass_union_le
import Theorems.Thm_AlmostLossless_length_matches_eq
import Theorems.Thm_AlmostLossless_listDecodeT_length_le
import Theorems.Thm_AlmostLossless_scanCost_fst
import Theorems.Thm_AlmostLossless_scanCost_snd

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Finset BigOperators NonArchInfoTheory AlmostLossless
variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}

theorem solution (μ : FinProbDist α) {H : Fin K → α → Fin M} {T : ℕ}
    (hI : IndepT H T) (hK : 0 < K) (hM : 0 < M)
    (l : List α) (hnd : l.Nodup) (δ : ℝ) (hδ : setMass μ (l.toFinset)ᶜ ≤ δ) :
    ∃ k : Fin K,
      setMass μ (Finset.univ.filter
          (fun x => ¬ (listHashScheme T l (H k)).Succeeds x))
          ≤ δ + (l.length.choose T : ℝ) / (M : ℝ) ^ T
      ∧ (∀ i : Fin M, ((listHashScheme T l (H k)).dec i).length ≤ T)
      ∧ ∀ i : Fin M, (scanCost (H k) i l).2 = l.length := by
  classical
  obtain ⟨k, hk⟩ := exists_good_key_indepT μ hI hK l.toFinset Finset.univ
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMT : (0 : ℝ) < (M : ℝ) ^ T := by positivity
  have hcard : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnd
  set C : Finset α :=
    Finset.univ.filter (fun x => T ≤ (collisionSet H k l.toFinset x).card) with hC
  have hCbound : setMass μ C ≤ (l.length.choose T : ℝ) / (M : ℝ) ^ T := by
    rw [le_div_iff₀ hMT]
    have h2 := hk
    rw [setMass_univ, mul_one, hcard] at h2
    linarith [h2]
  refine ⟨k, ?_, fun i => listDecodeT_length_le T _ l i, fun i => scanCost_snd _ _ _⟩
  have hsub : Finset.univ.filter (fun x => ¬ (listHashScheme T l (H k)).Succeeds x)
      ⊆ (l.toFinset)ᶜ ∪ C := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Finset.mem_union]
    by_cases hxl : x ∈ l.toFinset
    · right
      rw [hC, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hlt
      push_neg at hlt
      refine hx ?_
      have hxl' : x ∈ l := List.mem_toFinset.mp hxl
      have hlen : ((scanCost (H k) (H k x) l).1).length ≤ T := by
        have := length_matches_eq (H k) hnd hxl'
        have hcc : (collisionSet (fun _ : Fin 1 => H k) 0 l.toFinset x).card
            = (collisionSet H k l.toFinset x).card := by
          unfold collisionSet; rfl
        omega
      show x ∈ listDecodeT T (H k) l ((listHashScheme T l (H k)).enc x)
      unfold listHashScheme listDecodeT
      simp only [if_pos hlen]
      rw [scanCost_fst, List.mem_filter]
      exact ⟨hxl', by simp⟩
    · left; exact Finset.mem_compl.mpr hxl
  calc setMass μ (Finset.univ.filter (fun x => ¬ (listHashScheme T l (H k)).Succeeds x))
      ≤ setMass μ ((l.toFinset)ᶜ ∪ C) := setMass_mono μ hsub
    _ ≤ setMass μ (l.toFinset)ᶜ + setMass μ C := setMass_union_le μ _ _
    _ ≤ δ + (l.length.choose T : ℝ) / (M : ℝ) ^ T := add_le_add hδ hCbound


#print axioms solution
