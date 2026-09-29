-- Prove2me | solution 1 for mme_released_recursive_stage_region4_rate_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T15:47:52.750365+00:00
-- url     : https://prove2.me/submissions/4fb6fc54-e25d-4a05-aac0-9f2a6a15e413

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_ceiling_data
import Theorems.Thm_mme_certified_entropy_bridge
import Theorems.Thm_mme_certified_potential_ceiling
import Theorems.Thm_mme_certified_rate_entry
import Theorems.Thm_mme_released_recursive_stage_region4_coarse_floor
import Theorems.Thm_mme_released_recursive_stage_region4_penalty_ceil
import Theorems.Thm_mme_released_recursive_stage_region4_mix1_floor
import Theorems.Thm_mme_released_recursive_stage_region4_mix2_floor
import Theorems.Thm_mme_released_recursive_stage_region4_compat1_s0_h0
import Theorems.Thm_mme_released_recursive_stage_region4_compat1_s0_h1
import Theorems.Thm_mme_released_recursive_stage_region4_compat1_s1_h0
import Theorems.Thm_mme_released_recursive_stage_region4_compat1_s1_h1
import Theorems.Thm_mme_released_recursive_stage_region4_compat2_s0_h0
import Theorems.Thm_mme_released_recursive_stage_region4_compat2_s0_h1
import Theorems.Thm_mme_released_recursive_stage_region4_compat2_s1_h0
import Theorems.Thm_mme_released_recursive_stage_region4_compat2_s1_h1
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem solution :
    ((123252768423 * 6 * 10 ^ 48 : ℕ) : ℝ) <
      regionalRate (htotal3 4) (n3 4) (m3 4) (mu3 4) := by
  refine mme_certified_rate_entry.{0}.2 (htotal3 4) (n3 4) (m3 4) (mu3 4) _
    ?_ ?_ ?_
  · -- the X arm
    have hnum : ((123252768423 * 6 * 10 ^ 48 : ℕ) : ℝ) <
        ((739517600610609651326593771391531763774544795901863690000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 - ((805839192512687450805911455797608638685166296714000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 := by
      norm_num
    exact lt_of_lt_of_le hnum
      (sub_le_sub mme_released_recursive_stage_region4_coarse_floor
        mme_released_recursive_stage_region4_penalty_ceil)
  · -- the Y arm
    have hdec : compatibilityPotential 0 (mu3 4 1) =
        ∑ a : Fin 88, ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 4 a),
            if yzBoundary 0 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 4)) then
              ((∑ w, mu3 4 1 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 4 1 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr (a, j)) w : ℚ) : ℝ))) := by
      show RegionRealization.potential (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) = _
      rw [mme_certified_entropy_bridge.{0, 0}.2.1 (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)), Fintype.sum_sum_type,
        Finset.sum_add_distrib]
      congr 1
      · have hmid : (∑ c : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 4),
            if yzBoundary 0 c then
              ((∑ w, mu3 4 1 c w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 4 1 c) w : ℚ) : ℝ))
            else 0) =
            ∑ x : Fin 88, ∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 4 x),
              if yzBoundary 0 (⟨x, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 4)) then
                ((∑ w, mu3 4 1 ⟨x, b⟩ w : ℕ) : ℝ) *
                  entropy (fun w ↦ ((normQ (mu3 4 1 ⟨x, b⟩) w : ℚ) : ℝ))
              else 0 := by
          rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        refine Eq.trans ?_ hmid
        rw [← Finset.sum_filter]
        exact (Finset.sum_subtype _ (fun c ↦ by simp) (fun c ↦
          ((∑ w, mu3 4 1 c w : ℕ) : ℝ) *
            entropy (fun w ↦ ((normQ (mu3 4 1 c) w : ℚ) : ℝ)))).symm
      · rw [Fintype.sum_prod_type]
    have hsplit : (Finset.univ : Finset (Fin 88)) = (({(0 : Fin 88), (1 : Fin 88), (2 : Fin 88), (3 : Fin 88), (4 : Fin 88), (5 : Fin 88), (6 : Fin 88), (7 : Fin 88), (8 : Fin 88), (9 : Fin 88), (10 : Fin 88), (11 : Fin 88), (12 : Fin 88), (13 : Fin 88), (14 : Fin 88), (15 : Fin 88), (16 : Fin 88), (17 : Fin 88), (18 : Fin 88), (19 : Fin 88), (20 : Fin 88), (21 : Fin 88)} : Finset (Fin 88)) ∪ ({(22 : Fin 88), (23 : Fin 88), (24 : Fin 88), (25 : Fin 88), (26 : Fin 88), (27 : Fin 88), (28 : Fin 88), (29 : Fin 88), (30 : Fin 88), (31 : Fin 88), (32 : Fin 88), (33 : Fin 88), (34 : Fin 88), (35 : Fin 88), (36 : Fin 88), (37 : Fin 88), (38 : Fin 88), (39 : Fin 88), (40 : Fin 88), (41 : Fin 88), (42 : Fin 88), (43 : Fin 88)} : Finset (Fin 88))) ∪ (({(44 : Fin 88), (45 : Fin 88), (46 : Fin 88), (47 : Fin 88), (48 : Fin 88), (49 : Fin 88), (50 : Fin 88), (51 : Fin 88), (52 : Fin 88), (53 : Fin 88), (54 : Fin 88), (55 : Fin 88), (56 : Fin 88), (57 : Fin 88), (58 : Fin 88), (59 : Fin 88), (60 : Fin 88), (61 : Fin 88), (62 : Fin 88), (63 : Fin 88), (64 : Fin 88), (65 : Fin 88)} : Finset (Fin 88)) ∪ ({(66 : Fin 88), (67 : Fin 88), (68 : Fin 88), (69 : Fin 88), (70 : Fin 88), (71 : Fin 88), (72 : Fin 88), (73 : Fin 88), (74 : Fin 88), (75 : Fin 88), (76 : Fin 88), (77 : Fin 88), (78 : Fin 88), (79 : Fin 88), (80 : Fin 88), (81 : Fin 88), (82 : Fin 88), (83 : Fin 88), (84 : Fin 88), (85 : Fin 88), (86 : Fin 88), (87 : Fin 88)} : Finset (Fin 88))) := by
      decide +kernel
    have hK : compatibilityPotential 0 (mu3 4 1) ≤ ((784231733135629507348092336052975789711015244210422970643604588251000000000000000000000000 : ℕ) : ℝ)/10^30 := by
      rw [hdec, hsplit, Finset.sum_union (by decide +kernel),
        Finset.sum_union (by decide +kernel), Finset.sum_union (by decide +kernel)]
      refine le_trans (add_le_add
        (add_le_add mme_released_recursive_stage_region4_compat1_s0_h0
          mme_released_recursive_stage_region4_compat1_s0_h1)
        (add_le_add mme_released_recursive_stage_region4_compat1_s1_h0
          mme_released_recursive_stage_region4_compat1_s1_h1)) (le_of_eq ?_)
      push_cast
      ring
    have hnum : ((123252768423 * 6 * 10 ^ 48 : ℕ) : ℝ) <
        ((1523748940818048305055260642782545475184790132330285494000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 - ((784231733135629507348092336052975789711015244210422970643604588251000000000000000000000000 : ℕ) : ℝ)/10^30 := by
      norm_num
    exact lt_of_lt_of_le hnum
      (sub_le_sub mme_released_recursive_stage_region4_mix1_floor hK)
  · -- the Z arm
    have hdec : compatibilityPotential 1 (mu3 4 2) =
        ∑ a : Fin 88, ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 4 a),
            if yzBoundary 1 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 4)) then
              ((∑ w, mu3 4 2 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 4 2 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) (Sum.inr (a, j)) w : ℚ) : ℝ))) := by
      show RegionRealization.potential (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)) = _
      rw [mme_certified_entropy_bridge.{0, 0}.2.1 (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu3 4 2)), Fintype.sum_sum_type,
        Finset.sum_add_distrib]
      congr 1
      · have hmid : (∑ c : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 4),
            if yzBoundary 1 c then
              ((∑ w, mu3 4 2 c w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 4 2 c) w : ℚ) : ℝ))
            else 0) =
            ∑ x : Fin 88, ∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 4 x),
              if yzBoundary 1 (⟨x, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 4)) then
                ((∑ w, mu3 4 2 ⟨x, b⟩ w : ℕ) : ℝ) *
                  entropy (fun w ↦ ((normQ (mu3 4 2 ⟨x, b⟩) w : ℚ) : ℝ))
              else 0 := by
          rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        refine Eq.trans ?_ hmid
        rw [← Finset.sum_filter]
        exact (Finset.sum_subtype _ (fun c ↦ by simp) (fun c ↦
          ((∑ w, mu3 4 2 c w : ℕ) : ℝ) *
            entropy (fun w ↦ ((normQ (mu3 4 2 c) w : ℚ) : ℝ)))).symm
      · rw [Fintype.sum_prod_type]
    have hsplit : (Finset.univ : Finset (Fin 88)) = (({(0 : Fin 88), (1 : Fin 88), (2 : Fin 88), (3 : Fin 88), (4 : Fin 88), (5 : Fin 88), (6 : Fin 88), (7 : Fin 88), (8 : Fin 88), (9 : Fin 88), (10 : Fin 88), (11 : Fin 88), (12 : Fin 88), (13 : Fin 88), (14 : Fin 88), (15 : Fin 88), (16 : Fin 88), (17 : Fin 88), (18 : Fin 88), (19 : Fin 88), (20 : Fin 88), (21 : Fin 88)} : Finset (Fin 88)) ∪ ({(22 : Fin 88), (23 : Fin 88), (24 : Fin 88), (25 : Fin 88), (26 : Fin 88), (27 : Fin 88), (28 : Fin 88), (29 : Fin 88), (30 : Fin 88), (31 : Fin 88), (32 : Fin 88), (33 : Fin 88), (34 : Fin 88), (35 : Fin 88), (36 : Fin 88), (37 : Fin 88), (38 : Fin 88), (39 : Fin 88), (40 : Fin 88), (41 : Fin 88), (42 : Fin 88), (43 : Fin 88)} : Finset (Fin 88))) ∪ (({(44 : Fin 88), (45 : Fin 88), (46 : Fin 88), (47 : Fin 88), (48 : Fin 88), (49 : Fin 88), (50 : Fin 88), (51 : Fin 88), (52 : Fin 88), (53 : Fin 88), (54 : Fin 88), (55 : Fin 88), (56 : Fin 88), (57 : Fin 88), (58 : Fin 88), (59 : Fin 88), (60 : Fin 88), (61 : Fin 88), (62 : Fin 88), (63 : Fin 88), (64 : Fin 88), (65 : Fin 88)} : Finset (Fin 88)) ∪ ({(66 : Fin 88), (67 : Fin 88), (68 : Fin 88), (69 : Fin 88), (70 : Fin 88), (71 : Fin 88), (72 : Fin 88), (73 : Fin 88), (74 : Fin 88), (75 : Fin 88), (76 : Fin 88), (77 : Fin 88), (78 : Fin 88), (79 : Fin 88), (80 : Fin 88), (81 : Fin 88), (82 : Fin 88), (83 : Fin 88), (84 : Fin 88), (85 : Fin 88), (86 : Fin 88), (87 : Fin 88)} : Finset (Fin 88))) := by
      decide +kernel
    have hK : compatibilityPotential 1 (mu3 4 2) ≤ ((736656681957656203292689481307676894518844489335599866595813442256000000000000000000000000 : ℕ) : ℝ)/10^30 := by
      rw [hdec, hsplit, Finset.sum_union (by decide +kernel),
        Finset.sum_union (by decide +kernel), Finset.sum_union (by decide +kernel)]
      refine le_trans (add_le_add
        (add_le_add mme_released_recursive_stage_region4_compat2_s0_h0
          mme_released_recursive_stage_region4_compat2_s0_h1)
        (add_le_add mme_released_recursive_stage_region4_compat2_s1_h0
          mme_released_recursive_stage_region4_compat2_s1_h1)) (le_of_eq ?_)
      push_cast
      ring
    have hnum : ((123252768423 * 6 * 10 ^ 48 : ℕ) : ℝ) <
        ((1476173890581225823129735940247839590155772076355856709000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 - ((736656681957656203292689481307676894518844489335599866595813442256000000000000000000000000 : ℕ) : ℝ)/10^30 := by
      norm_num
    exact lt_of_lt_of_le hnum
      (sub_le_sub mme_released_recursive_stage_region4_mix2_floor hK)
