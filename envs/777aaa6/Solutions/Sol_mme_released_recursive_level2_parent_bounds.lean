-- Prove2me | solution 1 for mme_released_recursive_level2_parent_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T01:28:10.013288+00:00
-- url     : https://prove2.me/submissions/70c823d5-48d1-4ea3-8e78-e6f04aaae3ad

import Mathlib
import Theorems.Thm_mme_released_recursive_level2_cert0
import Theorems.Thm_mme_released_recursive_level2_cert1
import Theorems.Thm_mme_released_recursive_level2_cert2
import Theorems.Thm_mme_released_recursive_level2_cert3
import Theorems.Thm_mme_released_recursive_level2_cert4
import Theorems.Thm_mme_released_recursive_level2_cert5
import Theorems.Thm_mme_released_recursive_level2_cert6
import Theorems.Thm_mme_released_recursive_level2_cert7
import Theorems.Thm_mme_released_recursive_level2_cert8
import Theorems.Thm_mme_released_recursive_level2_cert9
import Theorems.Thm_mme_released_recursive_level2_cert10
import Theorems.Thm_mme_released_recursive_level2_cert11
import Definitions.Def_mme_released_recursive_level2_sum_data
import Definitions.Def_mme_released_recursive_level2_cert_data
import Definitions.Def_mme_released_recursive_level2_uniform_data
import Definitions.Def_mme_released_recursive_level2_floor_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data
import Theorems.Thm_mme_released_recursive_level2_floor_cases
import Theorems.Thm_mme_released_recursive_level2_potential_floor

open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


namespace MME.L2Cert

/-- Every region's certificate, from the twelve published chunks. -/
theorem cert_all (r : Fin 1104) :
    ((certNum r : Int) : ℚ)/10^30 ≤ regFloor (certMode r) r (certE r) := by
  rcases lt_or_ge r.val 92 with h0 | h0
  · have hr : (⟨0 + (r.val - 0), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 0 + (r.val - 0) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_cert0 ⟨r.val - 0, by omega⟩
  rcases lt_or_ge r.val 184 with h1 | h1
  · have hr : (⟨92 + (r.val - 92), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 92 + (r.val - 92) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_cert1 ⟨r.val - 92, by omega⟩
  rcases lt_or_ge r.val 276 with h2 | h2
  · have hr : (⟨184 + (r.val - 184), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 184 + (r.val - 184) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_cert2 ⟨r.val - 184, by omega⟩
  rcases lt_or_ge r.val 368 with h3 | h3
  · have hr : (⟨276 + (r.val - 276), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 276 + (r.val - 276) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_cert3 ⟨r.val - 276, by omega⟩
  rcases lt_or_ge r.val 460 with h4 | h4
  · have hr : (⟨368 + (r.val - 368), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 368 + (r.val - 368) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_cert4 ⟨r.val - 368, by omega⟩
  rcases lt_or_ge r.val 552 with h5 | h5
  · have hr : (⟨460 + (r.val - 460), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 460 + (r.val - 460) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_cert5 ⟨r.val - 460, by omega⟩
  rcases lt_or_ge r.val 644 with h6 | h6
  · have hr : (⟨552 + (r.val - 552), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 552 + (r.val - 552) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_cert6 ⟨r.val - 552, by omega⟩
  rcases lt_or_ge r.val 736 with h7 | h7
  · have hr : (⟨644 + (r.val - 644), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 644 + (r.val - 644) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_cert7 ⟨r.val - 644, by omega⟩
  rcases lt_or_ge r.val 828 with h8 | h8
  · have hr : (⟨736 + (r.val - 736), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 736 + (r.val - 736) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_cert8 ⟨r.val - 736, by omega⟩
  rcases lt_or_ge r.val 920 with h9 | h9
  · have hr : (⟨828 + (r.val - 828), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 828 + (r.val - 828) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_cert9 ⟨r.val - 828, by omega⟩
  rcases lt_or_ge r.val 1012 with h10 | h10
  · have hr : (⟨920 + (r.val - 920), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 920 + (r.val - 920) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_cert10 ⟨r.val - 920, by omega⟩
  have hr : (⟨1012 + (r.val - 1012), by omega⟩ : Fin 1104) = r := by
    apply Fin.ext
    show 1012 + (r.val - 1012) = r.val
    omega
  rw [← hr]
  exact mme_released_recursive_level2_cert11 ⟨r.val - 1012, by omega⟩

/-- The mode whose parent grade is two is exactly the certificate's parametric mode. -/
theorem mode_iff (r : Fin 1104) (i : Fin 3) : parent2 r i = 2 ↔ certMode r = i := by
  revert r i
  decide +kernel

theorem gTab_le (i : Fin 3) (r : Fin 1104) :
    ((gTab i r : Int) : ℚ)/10^30 ≤ regFloor i r (ETab i r) := by
  unfold gTab ETab
  by_cases h : certMode r = i
  · rw [if_pos h, if_pos h, ← h]
    exact cert_all r
  · rw [if_neg h, if_neg h]
    rw [mme_released_recursive_level2_floor_cases.2.2.1 i r
      (fun hc ↦ h ((mode_iff r i).mp hc)),
      mme_released_recursive_level2_floor_cases.1.1]
    norm_num

/-- A certified rational floor for a level-two parent potential, as one integer over `10 ^ 30`. -/
theorem parent_bound (i : Fin 3) :
    (((∑ r : Fin 1104, (n2 r : Int) * gTab i r : Int) : ℚ) : ℝ)/10^30 ≤
      parentPotential htotal2 n2 m2 (mu2 i) := by
  have h := mme_released_recursive_level2_potential_floor.2.2.2 i (ETab i)
    (fun r ↦ ((gTab i r : Int) : ℚ)/10^30) (fun r ↦ gTab_le i r)
  refine le_trans (le_of_eq ?_) h
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun r _ ↦ ?_)
  ring


end MME.L2Cert

theorem solution :
    (∀ i : Fin 3,
      (((∑ r : Fin 1104, (n2 r : Int) * gTab i r : Int) : ℚ) : ℝ)/10^30 ≤
        parentPotential htotal2 n2 m2 (mu2 i)) ∧
    (∑ r : Fin 1104, (n2 r : Int) * gTab 0 r) = 3515806618502173629491594525557823285980675975401445058912361661975000000000000000000000000 ∧
    (∑ r : Fin 1104, (n2 r : Int) * gTab 1 r) = 3515806618566367168009682512805551299923841462883523781856375661355000000000000000000000000 ∧
    (∑ r : Fin 1104, (n2 r : Int) * gTab 2 r) = 3515806618472678994050003868483823051612957705917546732375201127458000000000000000000000000 := by
  refine ⟨fun i ↦ MME.L2Cert.parent_bound i, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
