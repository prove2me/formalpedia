-- Prove2me | solution 1 for mme_released_recursive_level3_cell_forms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T05:17:15.041868+00:00
-- url     : https://prove2.me/submissions/0c37ee01-c6ee-4e15-a0c3-8d21561d2dda

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
open BigOperators MME MME.RecursiveYZ MME.RecStage
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem jwA004_0 (s : ℕ) : jw 0 0 4 s 0 0 2 = D := by
  norm_num [jw, D]
theorem jwA004_1 (s : ℕ) : jw 0 0 4 s 0 1 1 = 0 := by
  norm_num [jw, D]
theorem jwA004_2 (s : ℕ) : jw 0 0 4 s 0 2 0 = 0 := by
  norm_num [jw, D]
theorem jwA004_3 (s : ℕ) : jw 0 0 4 s 1 0 1 = 0 := by
  norm_num [jw, D]
theorem jwA004_4 (s : ℕ) : jw 0 0 4 s 1 1 0 = 0 := by
  norm_num [jw, D]
theorem jwA004_5 (s : ℕ) : jw 0 0 4 s 2 0 0 = 0 := by
  norm_num [jw, D]
theorem jwA013_0 (s : ℕ) : jw 0 1 3 s 0 0 2 = D / 2 := by
  norm_num [jw, D]
theorem jwA013_1 (s : ℕ) : jw 0 1 3 s 0 1 1 = D / 2 := by
  norm_num [jw, D]
theorem jwA013_2 (s : ℕ) : jw 0 1 3 s 0 2 0 = 0 := by
  norm_num [jw, D]
theorem jwA013_3 (s : ℕ) : jw 0 1 3 s 1 0 1 = 0 := by
  norm_num [jw, D]
theorem jwA013_4 (s : ℕ) : jw 0 1 3 s 1 1 0 = 0 := by
  norm_num [jw, D]
theorem jwA013_5 (s : ℕ) : jw 0 1 3 s 2 0 0 = 0 := by
  norm_num [jw, D]
theorem jwA022_0 (s : ℕ) : jw 0 2 2 s 0 0 2 = s := by
  norm_num [jw, D]
theorem jwA022_1 (s : ℕ) : jw 0 2 2 s 0 1 1 = D - 2 * s := by
  norm_num [jw, D]
theorem jwA022_2 (s : ℕ) : jw 0 2 2 s 0 2 0 = s := by
  norm_num [jw, D]
theorem jwA022_3 (s : ℕ) : jw 0 2 2 s 1 0 1 = 0 := by
  norm_num [jw, D]
theorem jwA022_4 (s : ℕ) : jw 0 2 2 s 1 1 0 = 0 := by
  norm_num [jw, D]
theorem jwA022_5 (s : ℕ) : jw 0 2 2 s 2 0 0 = 0 := by
  norm_num [jw, D]
theorem jwA031_0 (s : ℕ) : jw 0 3 1 s 0 0 2 = 0 := by
  norm_num [jw, D]
theorem jwA031_1 (s : ℕ) : jw 0 3 1 s 0 1 1 = D / 2 := by
  norm_num [jw, D]
theorem jwA031_2 (s : ℕ) : jw 0 3 1 s 0 2 0 = D / 2 := by
  norm_num [jw, D]
theorem jwA031_3 (s : ℕ) : jw 0 3 1 s 1 0 1 = 0 := by
  norm_num [jw, D]
theorem jwA031_4 (s : ℕ) : jw 0 3 1 s 1 1 0 = 0 := by
  norm_num [jw, D]
theorem jwA031_5 (s : ℕ) : jw 0 3 1 s 2 0 0 = 0 := by
  norm_num [jw, D]
theorem jwA040_0 (s : ℕ) : jw 0 4 0 s 0 0 2 = 0 := by
  norm_num [jw, D]
theorem jwA040_1 (s : ℕ) : jw 0 4 0 s 0 1 1 = 0 := by
  norm_num [jw, D]
theorem jwA040_2 (s : ℕ) : jw 0 4 0 s 0 2 0 = D := by
  norm_num [jw, D]
theorem jwA040_3 (s : ℕ) : jw 0 4 0 s 1 0 1 = 0 := by
  norm_num [jw, D]
theorem jwA040_4 (s : ℕ) : jw 0 4 0 s 1 1 0 = 0 := by
  norm_num [jw, D]
theorem jwA040_5 (s : ℕ) : jw 0 4 0 s 2 0 0 = 0 := by
  norm_num [jw, D]
theorem jwA103_0 (s : ℕ) : jw 1 0 3 s 0 0 2 = D / 2 := by
  norm_num [jw, D]
theorem jwA103_1 (s : ℕ) : jw 1 0 3 s 0 1 1 = 0 := by
  norm_num [jw, D]
theorem jwA103_2 (s : ℕ) : jw 1 0 3 s 0 2 0 = 0 := by
  norm_num [jw, D]
theorem jwA103_3 (s : ℕ) : jw 1 0 3 s 1 0 1 = D / 2 := by
  norm_num [jw, D]
theorem jwA103_4 (s : ℕ) : jw 1 0 3 s 1 1 0 = 0 := by
  norm_num [jw, D]
theorem jwA103_5 (s : ℕ) : jw 1 0 3 s 2 0 0 = 0 := by
  norm_num [jw, D]
theorem jwA112_0 (s : ℕ) : jw 1 1 2 s 0 0 2 = s := by
  norm_num [jw, D]
theorem jwA112_1 (s : ℕ) : jw 1 1 2 s 0 1 1 = D / 2 - s := by
  norm_num [jw, D]
theorem jwA112_2 (s : ℕ) : jw 1 1 2 s 0 2 0 = 0 := by
  norm_num [jw, D]
theorem jwA112_3 (s : ℕ) : jw 1 1 2 s 1 0 1 = D / 2 - s := by
  norm_num [jw, D]
theorem jwA112_4 (s : ℕ) : jw 1 1 2 s 1 1 0 = s := by
  norm_num [jw, D]
theorem jwA112_5 (s : ℕ) : jw 1 1 2 s 2 0 0 = 0 := by
  norm_num [jw, D]
theorem jwA121_0 (s : ℕ) : jw 1 2 1 s 0 0 2 = 0 := by
  norm_num [jw, D]
theorem jwA121_1 (s : ℕ) : jw 1 2 1 s 0 1 1 = D / 2 - s := by
  norm_num [jw, D]
theorem jwA121_2 (s : ℕ) : jw 1 2 1 s 0 2 0 = s := by
  norm_num [jw, D]
theorem jwA121_3 (s : ℕ) : jw 1 2 1 s 1 0 1 = s := by
  norm_num [jw, D]
theorem jwA121_4 (s : ℕ) : jw 1 2 1 s 1 1 0 = D / 2 - s := by
  norm_num [jw, D]
theorem jwA121_5 (s : ℕ) : jw 1 2 1 s 2 0 0 = 0 := by
  norm_num [jw, D]
theorem jwA130_0 (s : ℕ) : jw 1 3 0 s 0 0 2 = 0 := by
  norm_num [jw, D]
theorem jwA130_1 (s : ℕ) : jw 1 3 0 s 0 1 1 = 0 := by
  norm_num [jw, D]
theorem jwA130_2 (s : ℕ) : jw 1 3 0 s 0 2 0 = D / 2 := by
  norm_num [jw, D]
theorem jwA130_3 (s : ℕ) : jw 1 3 0 s 1 0 1 = 0 := by
  norm_num [jw, D]
theorem jwA130_4 (s : ℕ) : jw 1 3 0 s 1 1 0 = D / 2 := by
  norm_num [jw, D]
theorem jwA130_5 (s : ℕ) : jw 1 3 0 s 2 0 0 = 0 := by
  norm_num [jw, D]
theorem jwA202_0 (s : ℕ) : jw 2 0 2 s 0 0 2 = s := by
  norm_num [jw, D]
theorem jwA202_1 (s : ℕ) : jw 2 0 2 s 0 1 1 = 0 := by
  norm_num [jw, D]
theorem jwA202_2 (s : ℕ) : jw 2 0 2 s 0 2 0 = 0 := by
  norm_num [jw, D]
theorem jwA202_3 (s : ℕ) : jw 2 0 2 s 1 0 1 = D - 2 * s := by
  norm_num [jw, D]
theorem jwA202_4 (s : ℕ) : jw 2 0 2 s 1 1 0 = 0 := by
  norm_num [jw, D]
theorem jwA202_5 (s : ℕ) : jw 2 0 2 s 2 0 0 = s := by
  norm_num [jw, D]
theorem jwA211_0 (s : ℕ) : jw 2 1 1 s 0 0 2 = 0 := by
  norm_num [jw, D]
theorem jwA211_1 (s : ℕ) : jw 2 1 1 s 0 1 1 = s := by
  norm_num [jw, D]
theorem jwA211_2 (s : ℕ) : jw 2 1 1 s 0 2 0 = 0 := by
  norm_num [jw, D]
theorem jwA211_3 (s : ℕ) : jw 2 1 1 s 1 0 1 = D / 2 - s := by
  norm_num [jw, D]
theorem jwA211_4 (s : ℕ) : jw 2 1 1 s 1 1 0 = D / 2 - s := by
  norm_num [jw, D]
theorem jwA211_5 (s : ℕ) : jw 2 1 1 s 2 0 0 = s := by
  norm_num [jw, D]
theorem jwA220_0 (s : ℕ) : jw 2 2 0 s 0 0 2 = 0 := by
  norm_num [jw, D]
theorem jwA220_1 (s : ℕ) : jw 2 2 0 s 0 1 1 = 0 := by
  norm_num [jw, D]
theorem jwA220_2 (s : ℕ) : jw 2 2 0 s 0 2 0 = s := by
  norm_num [jw, D]
theorem jwA220_3 (s : ℕ) : jw 2 2 0 s 1 0 1 = 0 := by
  norm_num [jw, D]
theorem jwA220_4 (s : ℕ) : jw 2 2 0 s 1 1 0 = D - 2 * s := by
  norm_num [jw, D]
theorem jwA220_5 (s : ℕ) : jw 2 2 0 s 2 0 0 = s := by
  norm_num [jw, D]
theorem jwA301_0 (s : ℕ) : jw 3 0 1 s 0 0 2 = 0 := by
  norm_num [jw, D]
theorem jwA301_1 (s : ℕ) : jw 3 0 1 s 0 1 1 = 0 := by
  norm_num [jw, D]
theorem jwA301_2 (s : ℕ) : jw 3 0 1 s 0 2 0 = 0 := by
  norm_num [jw, D]
theorem jwA301_3 (s : ℕ) : jw 3 0 1 s 1 0 1 = D / 2 := by
  norm_num [jw, D]
theorem jwA301_4 (s : ℕ) : jw 3 0 1 s 1 1 0 = 0 := by
  norm_num [jw, D]
theorem jwA301_5 (s : ℕ) : jw 3 0 1 s 2 0 0 = D / 2 := by
  norm_num [jw, D]
theorem jwA310_0 (s : ℕ) : jw 3 1 0 s 0 0 2 = 0 := by
  norm_num [jw, D]
theorem jwA310_1 (s : ℕ) : jw 3 1 0 s 0 1 1 = 0 := by
  norm_num [jw, D]
theorem jwA310_2 (s : ℕ) : jw 3 1 0 s 0 2 0 = 0 := by
  norm_num [jw, D]
theorem jwA310_3 (s : ℕ) : jw 3 1 0 s 1 0 1 = 0 := by
  norm_num [jw, D]
theorem jwA310_4 (s : ℕ) : jw 3 1 0 s 1 1 0 = D / 2 := by
  norm_num [jw, D]
theorem jwA310_5 (s : ℕ) : jw 3 1 0 s 2 0 0 = D / 2 := by
  norm_num [jw, D]
theorem jwA400_0 (s : ℕ) : jw 4 0 0 s 0 0 2 = 0 := by
  norm_num [jw, D]
theorem jwA400_1 (s : ℕ) : jw 4 0 0 s 0 1 1 = 0 := by
  norm_num [jw, D]
theorem jwA400_2 (s : ℕ) : jw 4 0 0 s 0 2 0 = 0 := by
  norm_num [jw, D]
theorem jwA400_3 (s : ℕ) : jw 4 0 0 s 1 0 1 = 0 := by
  norm_num [jw, D]
theorem jwA400_4 (s : ℕ) : jw 4 0 0 s 1 1 0 = 0 := by
  norm_num [jw, D]
theorem jwA400_5 (s : ℕ) : jw 4 0 0 s 2 0 0 = D := by
  norm_num [jw, D]

theorem solution :
    (∀ (ρ : Fin 6) (i : Fin 3) (r : Fin 88)
        (c : RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) (parent3 ρ r)),
      cellDist ρ i r c =
        (List.range 9).map (fun idx ↦
          childW (c.val 0).val (c.val 1).val (c.val 2).val (cellRec ρ r c).2 i.val
            (idx / 3) (idx % 3))) ∧
    ∀ s : ℕ, 2 * s ≤ D →
      ((List.range 9).map (fun idx ↦ childW 0 0 4 s 0 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 0 4 s 1 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 0 4 s 2 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, 0, 0, 0, D]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 1 3 s 0 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 1 3 s 1 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 1 3 s 2 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, D / 2, 0, D / 2, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 2 2 s 0 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 2 2 s 1 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 2 2 s 2 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 3 1 s 0 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 3 1 s 1 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, D / 2, 0, D / 2, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 3 1 s 2 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 4 0 s 0 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 4 0 s 1 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, 0, 0, 0, D]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 4 0 s 2 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 0 3 s 0 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 0 3 s 1 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 0 3 s 2 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, D / 2, 0, D / 2, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 1 2 s 0 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 1 2 s 1 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 1 2 s 2 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 2 1 s 0 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 2 1 s 1 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 2 1 s 2 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 3 0 s 0 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 3 0 s 1 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, D / 2, 0, D / 2, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 3 0 s 2 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 0 2 s 0 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 0 2 s 1 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 0 2 s 2 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 1 1 s 0 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 1 1 s 1 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 1 1 s 2 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 2 0 s 0 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 2 0 s 1 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 2 0 s 2 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 3 0 1 s 0 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, D / 2, 0, D / 2, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 3 0 1 s 1 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 3 0 1 s 2 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 3 1 0 s 0 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, D / 2, 0, D / 2, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 3 1 0 s 1 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 3 1 0 s 2 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 4 0 0 s 0 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, 0, 0, 0, D]) ∧
      ((List.range 9).map (fun idx ↦ childW 4 0 0 s 1 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 4 0 0 s 2 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  have range9 : ∀ f : ℕ → ℕ,
      (List.range 9).map f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8] :=
    fun _ ↦ rfl
  refine ⟨fun _ _ _ _ ↦ rfl, ?_⟩
  intro s hs
  unfold D at hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [range9]
    norm_num [childW, elemT, coord, jwA004_0, jwA004_1, jwA004_2, jwA004_3, jwA004_4, jwA004_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA004_0, jwA004_1, jwA004_2, jwA004_3, jwA004_4, jwA004_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA004_0, jwA004_1, jwA004_2, jwA004_3, jwA004_4, jwA004_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA013_0, jwA013_1, jwA013_2, jwA013_3, jwA013_4, jwA013_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA013_0, jwA013_1, jwA013_2, jwA013_3, jwA013_4, jwA013_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA013_0, jwA013_1, jwA013_2, jwA013_3, jwA013_4, jwA013_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA022_0, jwA022_1, jwA022_2, jwA022_3, jwA022_4, jwA022_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA022_0, jwA022_1, jwA022_2, jwA022_3, jwA022_4, jwA022_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA022_0, jwA022_1, jwA022_2, jwA022_3, jwA022_4, jwA022_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA031_0, jwA031_1, jwA031_2, jwA031_3, jwA031_4, jwA031_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA031_0, jwA031_1, jwA031_2, jwA031_3, jwA031_4, jwA031_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA031_0, jwA031_1, jwA031_2, jwA031_3, jwA031_4, jwA031_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA040_0, jwA040_1, jwA040_2, jwA040_3, jwA040_4, jwA040_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA040_0, jwA040_1, jwA040_2, jwA040_3, jwA040_4, jwA040_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA040_0, jwA040_1, jwA040_2, jwA040_3, jwA040_4, jwA040_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA103_0, jwA103_1, jwA103_2, jwA103_3, jwA103_4, jwA103_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA103_0, jwA103_1, jwA103_2, jwA103_3, jwA103_4, jwA103_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA103_0, jwA103_1, jwA103_2, jwA103_3, jwA103_4, jwA103_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA112_0, jwA112_1, jwA112_2, jwA112_3, jwA112_4, jwA112_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA112_0, jwA112_1, jwA112_2, jwA112_3, jwA112_4, jwA112_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA112_0, jwA112_1, jwA112_2, jwA112_3, jwA112_4, jwA112_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA121_0, jwA121_1, jwA121_2, jwA121_3, jwA121_4, jwA121_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA121_0, jwA121_1, jwA121_2, jwA121_3, jwA121_4, jwA121_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA121_0, jwA121_1, jwA121_2, jwA121_3, jwA121_4, jwA121_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA130_0, jwA130_1, jwA130_2, jwA130_3, jwA130_4, jwA130_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA130_0, jwA130_1, jwA130_2, jwA130_3, jwA130_4, jwA130_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA130_0, jwA130_1, jwA130_2, jwA130_3, jwA130_4, jwA130_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA202_0, jwA202_1, jwA202_2, jwA202_3, jwA202_4, jwA202_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA202_0, jwA202_1, jwA202_2, jwA202_3, jwA202_4, jwA202_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA202_0, jwA202_1, jwA202_2, jwA202_3, jwA202_4, jwA202_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA211_0, jwA211_1, jwA211_2, jwA211_3, jwA211_4, jwA211_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA211_0, jwA211_1, jwA211_2, jwA211_3, jwA211_4, jwA211_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA211_0, jwA211_1, jwA211_2, jwA211_3, jwA211_4, jwA211_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA220_0, jwA220_1, jwA220_2, jwA220_3, jwA220_4, jwA220_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA220_0, jwA220_1, jwA220_2, jwA220_3, jwA220_4, jwA220_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA220_0, jwA220_1, jwA220_2, jwA220_3, jwA220_4, jwA220_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA301_0, jwA301_1, jwA301_2, jwA301_3, jwA301_4, jwA301_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA301_0, jwA301_1, jwA301_2, jwA301_3, jwA301_4, jwA301_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA301_0, jwA301_1, jwA301_2, jwA301_3, jwA301_4, jwA301_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA310_0, jwA310_1, jwA310_2, jwA310_3, jwA310_4, jwA310_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA310_0, jwA310_1, jwA310_2, jwA310_3, jwA310_4, jwA310_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA310_0, jwA310_1, jwA310_2, jwA310_3, jwA310_4, jwA310_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA400_0, jwA400_1, jwA400_2, jwA400_3, jwA400_4, jwA400_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA400_0, jwA400_1, jwA400_2, jwA400_3, jwA400_4, jwA400_5, D]
    try omega
  · rw [range9]
    norm_num [childW, elemT, coord, jwA400_0, jwA400_1, jwA400_2, jwA400_3, jwA400_4, jwA400_5, D]
    try omega
