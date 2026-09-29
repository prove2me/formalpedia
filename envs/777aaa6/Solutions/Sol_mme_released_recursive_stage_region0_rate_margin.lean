-- Prove2me | solution 1 for mme_released_recursive_stage_region0_rate_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T15:43:13.447894+00:00
-- url     : https://prove2.me/submissions/f692e895-4f47-4aab-8410-4e0c3847f5f1

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_ceiling_data
import Theorems.Thm_mme_certified_entropy_bridge
import Theorems.Thm_mme_certified_potential_ceiling
import Theorems.Thm_mme_certified_rate_entry
import Theorems.Thm_mme_released_recursive_stage_region0_coarse_floor
import Theorems.Thm_mme_released_recursive_stage_region0_penalty_ceil
import Theorems.Thm_mme_released_recursive_stage_region0_mix1_floor
import Theorems.Thm_mme_released_recursive_stage_region0_mix2_floor
import Theorems.Thm_mme_released_recursive_stage_region0_compat1_s0_h0
import Theorems.Thm_mme_released_recursive_stage_region0_compat1_s0_h1
import Theorems.Thm_mme_released_recursive_stage_region0_compat1_s1_h0
import Theorems.Thm_mme_released_recursive_stage_region0_compat1_s1_h1
import Theorems.Thm_mme_released_recursive_stage_region0_compat2_s0_h0
import Theorems.Thm_mme_released_recursive_stage_region0_compat2_s0_h1
import Theorems.Thm_mme_released_recursive_stage_region0_compat2_s1_h0
import Theorems.Thm_mme_released_recursive_stage_region0_compat2_s1_h1
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem solution :
    ((122641998732 * 6 * 10 ^ 48 : ℕ) : ℝ) <
      regionalRate (htotal3 0) (n3 0) (m3 0) (mu3 0) := by
  refine mme_certified_rate_entry.{0}.2 (htotal3 0) (n3 0) (m3 0) (mu3 0) _
    ?_ ?_ ?_
  · -- the X arm
    have hnum : ((122641998732 * 6 * 10 ^ 48 : ℕ) : ℝ) <
        ((735852980828408872615626123927860111521137282486281063000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 - ((803305713246762811498483050908518760815154941676000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
      norm_num
    exact lt_of_lt_of_le hnum
      (sub_le_sub mme_released_recursive_stage_region0_coarse_floor
        mme_released_recursive_stage_region0_penalty_ceil)
  · -- the Y arm
    have hdec : compatibilityPotential 0 (mu3 0 1) =
        ∑ a : Fin 88, ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 a),
            if yzBoundary 0 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 1 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 1 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) (Sum.inr (a, j)) w : ℚ) : ℝ))) := by
      show RegionRealization.potential (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)) = _
      rw [mme_certified_entropy_bridge.{0, 0}.2.1 (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 0 1)), Fintype.sum_sum_type,
        Finset.sum_add_distrib]
      congr 1
      · have hmid : (∑ c : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0),
            if yzBoundary 0 c then
              ((∑ w, mu3 0 1 c w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 1 c) w : ℚ) : ℝ))
            else 0) =
            ∑ x : Fin 88, ∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 x),
              if yzBoundary 0 (⟨x, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
                ((∑ w, mu3 0 1 ⟨x, b⟩ w : ℕ) : ℝ) *
                  entropy (fun w ↦ ((normQ (mu3 0 1 ⟨x, b⟩) w : ℚ) : ℝ))
              else 0 := by
          rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        refine Eq.trans ?_ hmid
        rw [← Finset.sum_filter]
        exact (Finset.sum_subtype _ (fun c ↦ by simp) (fun c ↦
          ((∑ w, mu3 0 1 c w : ℕ) : ℝ) *
            entropy (fun w ↦ ((normQ (mu3 0 1 c) w : ℚ) : ℝ)))).symm
      · rw [Fintype.sum_prod_type]
    have hsplit : (Finset.univ : Finset (Fin 88)) = (({(0 : Fin 88), (1 : Fin 88), (2 : Fin 88), (3 : Fin 88), (4 : Fin 88), (5 : Fin 88), (6 : Fin 88), (7 : Fin 88), (8 : Fin 88), (9 : Fin 88), (10 : Fin 88), (11 : Fin 88), (12 : Fin 88), (13 : Fin 88), (14 : Fin 88), (15 : Fin 88), (16 : Fin 88), (17 : Fin 88), (18 : Fin 88), (19 : Fin 88), (20 : Fin 88), (21 : Fin 88)} : Finset (Fin 88)) ∪ ({(22 : Fin 88), (23 : Fin 88), (24 : Fin 88), (25 : Fin 88), (26 : Fin 88), (27 : Fin 88), (28 : Fin 88), (29 : Fin 88), (30 : Fin 88), (31 : Fin 88), (32 : Fin 88), (33 : Fin 88), (34 : Fin 88), (35 : Fin 88), (36 : Fin 88), (37 : Fin 88), (38 : Fin 88), (39 : Fin 88), (40 : Fin 88), (41 : Fin 88), (42 : Fin 88), (43 : Fin 88)} : Finset (Fin 88))) ∪ (({(44 : Fin 88), (45 : Fin 88), (46 : Fin 88), (47 : Fin 88), (48 : Fin 88), (49 : Fin 88), (50 : Fin 88), (51 : Fin 88), (52 : Fin 88), (53 : Fin 88), (54 : Fin 88), (55 : Fin 88), (56 : Fin 88), (57 : Fin 88), (58 : Fin 88), (59 : Fin 88), (60 : Fin 88), (61 : Fin 88), (62 : Fin 88), (63 : Fin 88), (64 : Fin 88), (65 : Fin 88)} : Finset (Fin 88)) ∪ ({(66 : Fin 88), (67 : Fin 88), (68 : Fin 88), (69 : Fin 88), (70 : Fin 88), (71 : Fin 88), (72 : Fin 88), (73 : Fin 88), (74 : Fin 88), (75 : Fin 88), (76 : Fin 88), (77 : Fin 88), (78 : Fin 88), (79 : Fin 88), (80 : Fin 88), (81 : Fin 88), (82 : Fin 88), (83 : Fin 88), (84 : Fin 88), (85 : Fin 88), (86 : Fin 88), (87 : Fin 88)} : Finset (Fin 88))) := by
      decide +kernel
    have hK : compatibilityPotential 0 (mu3 0 1) ≤ ((780267839142858306755044655667282316861649651511478281751247822632000000000000000000000000 : ℕ) : ℝ)/10^30 := by
      rw [hdec, hsplit, Finset.sum_union (by decide +kernel),
        Finset.sum_union (by decide +kernel), Finset.sum_union (by decide +kernel)]
      refine le_trans (add_le_add
        (add_le_add mme_released_recursive_stage_region0_compat1_s0_h0
          mme_released_recursive_stage_region0_compat1_s0_h1)
        (add_le_add mme_released_recursive_stage_region0_compat1_s1_h0
          mme_released_recursive_stage_region0_compat1_s1_h1)) (le_of_eq ?_)
      push_cast
      ring
    have hnum : ((122641998732 * 6 * 10 ^ 48 : ℕ) : ℝ) <
        ((1516120428877041962206481113818414064318210966468831313000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 - ((780267839142858306755044655667282316861649651511478281751247822632000000000000000000000000 : ℕ) : ℝ)/10^30 := by
      norm_num
    exact lt_of_lt_of_le hnum
      (sub_le_sub mme_released_recursive_stage_region0_mix1_floor hK)
  · -- the Z arm
    have hdec : compatibilityPotential 1 (mu3 0 2) =
        ∑ a : Fin 88, ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 a),
            if yzBoundary 1 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
              ((∑ w, mu3 0 2 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) (Sum.inr (a, j)) w : ℚ) : ℝ))) := by
      show RegionRealization.potential (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)) = _
      rw [mme_certified_entropy_bridge.{0, 0}.2.1 (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 0 2)), Fintype.sum_sum_type,
        Finset.sum_add_distrib]
      congr 1
      · have hmid : (∑ c : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0),
            if yzBoundary 1 c then
              ((∑ w, mu3 0 2 c w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 0 2 c) w : ℚ) : ℝ))
            else 0) =
            ∑ x : Fin 88, ∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 0 x),
              if yzBoundary 1 (⟨x, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 0)) then
                ((∑ w, mu3 0 2 ⟨x, b⟩ w : ℕ) : ℝ) *
                  entropy (fun w ↦ ((normQ (mu3 0 2 ⟨x, b⟩) w : ℚ) : ℝ))
              else 0 := by
          rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        refine Eq.trans ?_ hmid
        rw [← Finset.sum_filter]
        exact (Finset.sum_subtype _ (fun c ↦ by simp) (fun c ↦
          ((∑ w, mu3 0 2 c w : ℕ) : ℝ) *
            entropy (fun w ↦ ((normQ (mu3 0 2 c) w : ℚ) : ℝ)))).symm
      · rw [Fintype.sum_prod_type]
    have hsplit : (Finset.univ : Finset (Fin 88)) = (({(0 : Fin 88), (1 : Fin 88), (2 : Fin 88), (3 : Fin 88), (4 : Fin 88), (5 : Fin 88), (6 : Fin 88), (7 : Fin 88), (8 : Fin 88), (9 : Fin 88), (10 : Fin 88), (11 : Fin 88), (12 : Fin 88), (13 : Fin 88), (14 : Fin 88), (15 : Fin 88), (16 : Fin 88), (17 : Fin 88), (18 : Fin 88), (19 : Fin 88), (20 : Fin 88), (21 : Fin 88)} : Finset (Fin 88)) ∪ ({(22 : Fin 88), (23 : Fin 88), (24 : Fin 88), (25 : Fin 88), (26 : Fin 88), (27 : Fin 88), (28 : Fin 88), (29 : Fin 88), (30 : Fin 88), (31 : Fin 88), (32 : Fin 88), (33 : Fin 88), (34 : Fin 88), (35 : Fin 88), (36 : Fin 88), (37 : Fin 88), (38 : Fin 88), (39 : Fin 88), (40 : Fin 88), (41 : Fin 88), (42 : Fin 88), (43 : Fin 88)} : Finset (Fin 88))) ∪ (({(44 : Fin 88), (45 : Fin 88), (46 : Fin 88), (47 : Fin 88), (48 : Fin 88), (49 : Fin 88), (50 : Fin 88), (51 : Fin 88), (52 : Fin 88), (53 : Fin 88), (54 : Fin 88), (55 : Fin 88), (56 : Fin 88), (57 : Fin 88), (58 : Fin 88), (59 : Fin 88), (60 : Fin 88), (61 : Fin 88), (62 : Fin 88), (63 : Fin 88), (64 : Fin 88), (65 : Fin 88)} : Finset (Fin 88)) ∪ ({(66 : Fin 88), (67 : Fin 88), (68 : Fin 88), (69 : Fin 88), (70 : Fin 88), (71 : Fin 88), (72 : Fin 88), (73 : Fin 88), (74 : Fin 88), (75 : Fin 88), (76 : Fin 88), (77 : Fin 88), (78 : Fin 88), (79 : Fin 88), (80 : Fin 88), (81 : Fin 88), (82 : Fin 88), (83 : Fin 88), (84 : Fin 88), (85 : Fin 88), (86 : Fin 88), (87 : Fin 88)} : Finset (Fin 88))) := by
      decide +kernel
    have hK : compatibilityPotential 1 (mu3 0 2) ≤ ((732983021924818026135996310303207421728267328920268725515646340119000000000000000000000000 : ℕ) : ℝ)/10^30 := by
      rw [hdec, hsplit, Finset.sum_union (by decide +kernel),
        Finset.sum_union (by decide +kernel), Finset.sum_union (by decide +kernel)]
      refine le_trans (add_le_add
        (add_le_add mme_released_recursive_stage_region0_compat2_s0_h0
          mme_released_recursive_stage_region0_compat2_s0_h1)
        (add_le_add mme_released_recursive_stage_region0_compat2_s1_h0
          mme_released_recursive_stage_region0_compat2_s1_h1)) (le_of_eq ?_)
      push_cast
      ring
    have hnum : ((122641998732 * 6 * 10 ^ 48 : ℕ) : ℝ) <
        ((1468835612336557740334044303566260566468492337391676998000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 - ((732983021924818026135996310303207421728267328920268725515646340119000000000000000000000000 : ℕ) : ℝ)/10^30 := by
      norm_num
    exact lt_of_lt_of_le hnum
      (sub_le_sub mme_released_recursive_stage_region0_mix2_floor hK)
