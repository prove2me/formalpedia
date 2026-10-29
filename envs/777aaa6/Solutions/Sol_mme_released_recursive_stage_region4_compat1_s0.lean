-- Prove2me | solution 1 for mme_released_recursive_stage_region4_compat1_s0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:09:24.336092+00:00
-- url     : https://prove2.me/submissions/2179c968-0470-4dbf-8f15-47ea54b7ef6b

import Mathlib
import Theorems.Thm_mme_released_recursive_stage_region4_compat1_s0_h0
import Theorems.Thm_mme_released_recursive_stage_region4_compat1_s0_h1
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_ceiling_data
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem split_sum {f : Fin 88 → ℝ} {S S0 S1 : Finset (Fin 88)} (h : S = S0 ∪ S1)
    (hd : Disjoint S0 S1) {B0 B1 B : ℝ} (h0 : ∑ a ∈ S0, f a ≤ B0) (h1 : ∑ a ∈ S1, f a ≤ B1)
    (hB : B0 + B1 ≤ B) : ∑ a ∈ S, f a ≤ B := by
  rw [h, Finset.sum_union hd]; linarith

theorem solution :
    ∑ a ∈ (({(0 : Fin 88), (1 : Fin 88), (2 : Fin 88), (3 : Fin 88), (4 : Fin 88), (5 : Fin 88), (6 : Fin 88), (7 : Fin 88), (8 : Fin 88), (9 : Fin 88), (10 : Fin 88), (11 : Fin 88), (12 : Fin 88), (13 : Fin 88), (14 : Fin 88), (15 : Fin 88), (16 : Fin 88), (17 : Fin 88), (18 : Fin 88), (19 : Fin 88), (20 : Fin 88), (21 : Fin 88), (22 : Fin 88), (23 : Fin 88), (24 : Fin 88), (25 : Fin 88), (26 : Fin 88), (27 : Fin 88), (28 : Fin 88), (29 : Fin 88), (30 : Fin 88), (31 : Fin 88), (32 : Fin 88), (33 : Fin 88), (34 : Fin 88), (35 : Fin 88), (36 : Fin 88), (37 : Fin 88), (38 : Fin 88), (39 : Fin 88), (40 : Fin 88), (41 : Fin 88), (42 : Fin 88), (43 : Fin 88)}) : Finset (Fin 88)),
        ((∑ b : Split (2 * 2 ^ (2 - 1)) (parent3 4 a),
            if yzBoundary 0 (⟨a, b⟩ : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 4)) then
              ((∑ w, mu3 4 1 ⟨a, b⟩ w : ℕ) : ℝ) *
                entropy (fun w ↦ ((normQ (mu3 4 1 ⟨a, b⟩) w : ℚ) : ℝ))
            else 0)
          + ∑ j : Fin (2 * 2 ^ (2 - 1) + 1),
              ((∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1) (Sum.inr (a, j)) w : ℕ) : ℝ) *
                entropy (fun w ↦ ((freqQ (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu3 4 1)) (Sum.inr (a, j)) w : ℚ) : ℝ))) ≤
      ((351081161898302697270550388496411524659535547849153973139365014870000000000000000000000000 : ℕ) : ℝ)/10^30 := by
  exact split_sum (by decide) (by decide) mme_released_recursive_stage_region4_compat1_s0_h0 mme_released_recursive_stage_region4_compat1_s0_h1 (by norm_num)

