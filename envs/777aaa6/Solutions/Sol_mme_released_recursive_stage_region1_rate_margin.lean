-- Prove2me | solution 1 for mme_released_recursive_stage_region1_rate_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T15:47:22.423983+00:00
-- url     : https://prove2.me/submissions/af0bcb64-78cd-45e7-a674-97bd4529b35a

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_ceiling_data
import Theorems.Thm_mme_certified_entropy_bridge
import Theorems.Thm_mme_certified_potential_ceiling
import Theorems.Thm_mme_certified_rate_entry
import Theorems.Thm_mme_released_recursive_stage_region1_coarse_floor
import Theorems.Thm_mme_released_recursive_stage_region1_penalty_ceil
import Theorems.Thm_mme_released_recursive_stage_region1_mix1_floor
import Theorems.Thm_mme_released_recursive_stage_region1_mix2_floor
import Theorems.Thm_mme_released_recursive_stage_region1_compat1_s0_h0
import Theorems.Thm_mme_released_recursive_stage_region1_compat1_s0_h1
import Theorems.Thm_mme_released_recursive_stage_region1_compat1_s1_h0
import Theorems.Thm_mme_released_recursive_stage_region1_compat1_s1_h1
import Theorems.Thm_mme_released_recursive_stage_region1_compat2_s0_h0
import Theorems.Thm_mme_released_recursive_stage_region1_compat2_s0_h1
import Theorems.Thm_mme_released_recursive_stage_region1_compat2_s1_h0
import Theorems.Thm_mme_released_recursive_stage_region1_compat2_s1_h1
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem solution :
    ((122627240242 * 6 * 10 ^ 48 : ℕ) : ℝ) <
      regionalRate (htotal3 1) (n3 1) (m3 1) (mu3 1) := by
  refine mme_certified_rate_entry.{0}.2 (htotal3 1) (n3 1) (m3 1) (mu3 1) _
    ?_ ?_ ?_
  · -- the X arm
    have hnum : ((122627240242 * 6 * 10 ^ 48 : ℕ) : ℝ) <
        ((735764431905085349208569857096987811680834685659636238000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 - ((806290758639450817762753751715513287105041458170000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
      norm_num
    exact lt_of_lt_of_le hnum
      (sub_le_sub mme_released_recursive_stage_region1_coarse_floor
        mme_released_recursive_stage_region1_penalty_ceil)
  · -- the Y arm
    have hdec : compatibilityPotential 0 (mu3 1 1) =
        ∑ a : Fin 88, ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 a),
            if yzBoundary 0 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 1 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) (Sum.inr (a, j)) w : ℚ) : ℝ))) := by
      show RegionRealization.potential (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)) = _
      rw [mme_certified_entropy_bridge.{0, 0}.2.1 (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 1 1)), Fintype.sum_sum_type,
        Finset.sum_add_distrib]
      congr 1
      · have hmid : (∑ c : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1),
            if yzBoundary 0 c then
              ((∑ w, mu3 1 1 c w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 1 c) w : ℚ) : ℝ))
            else 0) =
            ∑ x : Fin 88, ∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 x),
              if yzBoundary 0 (⟨x, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
                ((∑ w, mu3 1 1 ⟨x, b⟩ w : ℕ) : ℝ) *
                  entropy (fun w ↦ ((normQ (mu3 1 1 ⟨x, b⟩) w : ℚ) : ℝ))
              else 0 := by
          rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        refine Eq.trans ?_ hmid
        rw [← Finset.sum_filter]
        exact (Finset.sum_subtype _ (fun c ↦ by simp) (fun c ↦
          ((∑ w, mu3 1 1 c w : ℕ) : ℝ) *
            entropy (fun w ↦ ((normQ (mu3 1 1 c) w : ℚ) : ℝ)))).symm
      · rw [Fintype.sum_prod_type]
    have hsplit : (Finset.univ : Finset (Fin 88)) = (({(0 : Fin 88), (1 : Fin 88), (2 : Fin 88), (3 : Fin 88), (4 : Fin 88), (5 : Fin 88), (6 : Fin 88), (7 : Fin 88), (8 : Fin 88), (9 : Fin 88), (10 : Fin 88), (11 : Fin 88), (12 : Fin 88), (13 : Fin 88), (14 : Fin 88), (15 : Fin 88), (16 : Fin 88), (17 : Fin 88), (18 : Fin 88), (19 : Fin 88), (20 : Fin 88), (21 : Fin 88)} : Finset (Fin 88)) ∪ ({(22 : Fin 88), (23 : Fin 88), (24 : Fin 88), (25 : Fin 88), (26 : Fin 88), (27 : Fin 88), (28 : Fin 88), (29 : Fin 88), (30 : Fin 88), (31 : Fin 88), (32 : Fin 88), (33 : Fin 88), (34 : Fin 88), (35 : Fin 88), (36 : Fin 88), (37 : Fin 88), (38 : Fin 88), (39 : Fin 88), (40 : Fin 88), (41 : Fin 88), (42 : Fin 88), (43 : Fin 88)} : Finset (Fin 88))) ∪ (({(44 : Fin 88), (45 : Fin 88), (46 : Fin 88), (47 : Fin 88), (48 : Fin 88), (49 : Fin 88), (50 : Fin 88), (51 : Fin 88), (52 : Fin 88), (53 : Fin 88), (54 : Fin 88), (55 : Fin 88), (56 : Fin 88), (57 : Fin 88), (58 : Fin 88), (59 : Fin 88), (60 : Fin 88), (61 : Fin 88), (62 : Fin 88), (63 : Fin 88), (64 : Fin 88), (65 : Fin 88)} : Finset (Fin 88)) ∪ ({(66 : Fin 88), (67 : Fin 88), (68 : Fin 88), (69 : Fin 88), (70 : Fin 88), (71 : Fin 88), (72 : Fin 88), (73 : Fin 88), (74 : Fin 88), (75 : Fin 88), (76 : Fin 88), (77 : Fin 88), (78 : Fin 88), (79 : Fin 88), (80 : Fin 88), (81 : Fin 88), (82 : Fin 88), (83 : Fin 88), (84 : Fin 88), (85 : Fin 88), (86 : Fin 88), (87 : Fin 88)} : Finset (Fin 88))) := by
      decide +kernel
    have hK : compatibilityPotential 0 (mu3 1 1) ≤ ((780069401299087375556662043650549893463886369935057015083342670393000000000000000000000000 : ℕ) : ℝ)/10^30 := by
      rw [hdec, hsplit, Finset.sum_union (by decide +kernel),
        Finset.sum_union (by decide +kernel), Finset.sum_union (by decide +kernel)]
      refine le_trans (add_le_add
        (add_le_add mme_released_recursive_stage_region1_compat1_s0_h0
          mme_released_recursive_stage_region1_compat1_s0_h1)
        (add_le_add mme_released_recursive_stage_region1_compat1_s1_h0
          mme_released_recursive_stage_region1_compat1_s1_h1)) (le_of_eq ?_)
      push_cast
      ring
    have hnum : ((122627240242 * 6 * 10 ^ 48 : ℕ) : ℝ) <
        ((1515833440033496965869877336942703251910466681213239674000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 - ((780069401299087375556662043650549893463886369935057015083342670393000000000000000000000000 : ℕ) : ℝ)/10^30 := by
      norm_num
    exact lt_of_lt_of_le hnum
      (sub_le_sub mme_released_recursive_stage_region1_mix1_floor hK)
  · -- the Z arm
    have hdec : compatibilityPotential 1 (mu3 1 2) =
        ∑ a : Fin 88, ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 a),
            if yzBoundary 1 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
              ((∑ w, mu3 1 2 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 2 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) (Sum.inr (a, j)) w : ℚ) : ℝ))) := by
      show RegionRealization.potential (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)) = _
      rw [mme_certified_entropy_bridge.{0, 0}.2.1 (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 1 2)), Fintype.sum_sum_type,
        Finset.sum_add_distrib]
      congr 1
      · have hmid : (∑ c : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1),
            if yzBoundary 1 c then
              ((∑ w, mu3 1 2 c w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 1 2 c) w : ℚ) : ℝ))
            else 0) =
            ∑ x : Fin 88, ∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 1 x),
              if yzBoundary 1 (⟨x, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 1)) then
                ((∑ w, mu3 1 2 ⟨x, b⟩ w : ℕ) : ℝ) *
                  entropy (fun w ↦ ((normQ (mu3 1 2 ⟨x, b⟩) w : ℚ) : ℝ))
              else 0 := by
          rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        refine Eq.trans ?_ hmid
        rw [← Finset.sum_filter]
        exact (Finset.sum_subtype _ (fun c ↦ by simp) (fun c ↦
          ((∑ w, mu3 1 2 c w : ℕ) : ℝ) *
            entropy (fun w ↦ ((normQ (mu3 1 2 c) w : ℚ) : ℝ)))).symm
      · rw [Fintype.sum_prod_type]
    have hsplit : (Finset.univ : Finset (Fin 88)) = (({(0 : Fin 88), (1 : Fin 88), (2 : Fin 88), (3 : Fin 88), (4 : Fin 88), (5 : Fin 88), (6 : Fin 88), (7 : Fin 88), (8 : Fin 88), (9 : Fin 88), (10 : Fin 88), (11 : Fin 88), (12 : Fin 88), (13 : Fin 88), (14 : Fin 88), (15 : Fin 88), (16 : Fin 88), (17 : Fin 88), (18 : Fin 88), (19 : Fin 88), (20 : Fin 88), (21 : Fin 88)} : Finset (Fin 88)) ∪ ({(22 : Fin 88), (23 : Fin 88), (24 : Fin 88), (25 : Fin 88), (26 : Fin 88), (27 : Fin 88), (28 : Fin 88), (29 : Fin 88), (30 : Fin 88), (31 : Fin 88), (32 : Fin 88), (33 : Fin 88), (34 : Fin 88), (35 : Fin 88), (36 : Fin 88), (37 : Fin 88), (38 : Fin 88), (39 : Fin 88), (40 : Fin 88), (41 : Fin 88), (42 : Fin 88), (43 : Fin 88)} : Finset (Fin 88))) ∪ (({(44 : Fin 88), (45 : Fin 88), (46 : Fin 88), (47 : Fin 88), (48 : Fin 88), (49 : Fin 88), (50 : Fin 88), (51 : Fin 88), (52 : Fin 88), (53 : Fin 88), (54 : Fin 88), (55 : Fin 88), (56 : Fin 88), (57 : Fin 88), (58 : Fin 88), (59 : Fin 88), (60 : Fin 88), (61 : Fin 88), (62 : Fin 88), (63 : Fin 88), (64 : Fin 88), (65 : Fin 88)} : Finset (Fin 88)) ∪ ({(66 : Fin 88), (67 : Fin 88), (68 : Fin 88), (69 : Fin 88), (70 : Fin 88), (71 : Fin 88), (72 : Fin 88), (73 : Fin 88), (74 : Fin 88), (75 : Fin 88), (76 : Fin 88), (77 : Fin 88), (78 : Fin 88), (79 : Fin 88), (80 : Fin 88), (81 : Fin 88), (82 : Fin 88), (83 : Fin 88), (84 : Fin 88), (85 : Fin 88), (86 : Fin 88), (87 : Fin 88)} : Finset (Fin 88))) := by
      decide +kernel
    have hK : compatibilityPotential 1 (mu3 1 2) ≤ ((732914276818970994330630981247233838143244779753162458532420912766000000000000000000000000 : ℕ) : ℝ)/10^30 := by
      rw [hdec, hsplit, Finset.sum_union (by decide +kernel),
        Finset.sum_union (by decide +kernel), Finset.sum_union (by decide +kernel)]
      refine le_trans (add_le_add
        (add_le_add mme_released_recursive_stage_region1_compat2_s0_h0
          mme_released_recursive_stage_region1_compat2_s0_h1)
        (add_le_add mme_released_recursive_stage_region1_compat2_s1_h0
          mme_released_recursive_stage_region1_compat2_s1_h1)) (le_of_eq ?_)
      push_cast
      ring
    have hnum : ((122627240242 * 6 * 10 ^ 48 : ℕ) : ℝ) <
        ((1468678316335063709418101018263707426928961215700119434000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 - ((732914276818970994330630981247233838143244779753162458532420912766000000000000000000000000 : ℕ) : ℝ)/10^30 := by
      norm_num
    exact lt_of_lt_of_le hnum
      (sub_le_sub mme_released_recursive_stage_region1_mix2_floor hK)
