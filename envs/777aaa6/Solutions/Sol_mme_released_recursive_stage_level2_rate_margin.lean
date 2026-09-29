-- Prove2me | solution 1 for mme_released_recursive_stage_level2_rate_margin
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T05:45:25.206451+00:00
-- url     : https://prove2.me/submissions/45a76dcb-354f-49f7-bbe0-8f5c89b3a353
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mme_released_recursive_level2_pen0
import Theorems.Thm_mme_released_recursive_level2_pen1
import Theorems.Thm_mme_released_recursive_level2_pen2
import Theorems.Thm_mme_released_recursive_level2_pen3
import Theorems.Thm_mme_released_recursive_level2_pen4a
import Theorems.Thm_mme_released_recursive_level2_pen4b
import Theorems.Thm_mme_released_recursive_level2_pen5
import Theorems.Thm_mme_released_recursive_level2_pen6
import Theorems.Thm_mme_released_recursive_level2_pen7
import Theorems.Thm_mme_released_recursive_level2_pen8
import Theorems.Thm_mme_released_recursive_level2_pen9a
import Theorems.Thm_mme_released_recursive_level2_pen9b
import Theorems.Thm_mme_released_recursive_level2_pen10a
import Theorems.Thm_mme_released_recursive_level2_pen10b
import Theorems.Thm_mme_released_recursive_level2_pen11a
import Theorems.Thm_mme_released_recursive_level2_pen11b
import Theorems.Thm_mme_released_recursive_level2_pen12
import Theorems.Thm_mme_released_recursive_level2_pen13
import Theorems.Thm_mme_released_recursive_level2_pen14
import Theorems.Thm_mme_released_recursive_level2_pen15
import Theorems.Thm_mme_released_recursive_level2_pen16
import Theorems.Thm_mme_released_recursive_level2_pen17
import Theorems.Thm_mme_released_recursive_level2_pen18
import Theorems.Thm_mme_released_recursive_level2_pen19
import Theorems.Thm_mme_released_recursive_level2_pen20
import Theorems.Thm_mme_released_recursive_level2_pen21
import Theorems.Thm_mme_released_recursive_level2_pen22
import Theorems.Thm_mme_released_recursive_level2_pen23
import Definitions.Def_mme_released_recursive_level2_penalty_data
import Definitions.Def_mme_released_recursive_level2_sum_data
import Definitions.Def_mme_released_recursive_level2_cert_data
import Definitions.Def_mme_released_recursive_level2_uniform_data
import Definitions.Def_mme_released_recursive_level2_floor_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_released_recursive_level2_penalty_tools
import Theorems.Thm_mme_released_recursive_level2_parent_bounds
import Theorems.Thm_mme_released_recursive_level2_coarse
import Theorems.Thm_mme_released_recursive_level2_structure

open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MME.L2Cert

theorem pen_bound (r : Fin 1104) :
    Real.log 2 * entropyPenalty (fun c ↦ ((alphaQ r c : ℚ) : ℝ)) ≤
      (((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
          qvalQ (fun t ↦ ∑ i, PE r i (c.val i) t)) - 2 +
        ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
          (alphaQ r c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE r i (c.val i) t) : ℚ) : ℝ) :=
  mme_released_recursive_level2_penalty_tools.2.2.2.2.2.2.2 r

/-- Every region's penalty bound, from the published chunks. -/
theorem pen_all (r : Fin 1104) :
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
        qvalQ (fun t ↦ ∑ i, PE r i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
        (alphaQ r c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE r i (c.val i) t)) ≤ 1/(5 * 10^7) := by
  rcases lt_or_ge r.val 46 with h0 | h0
  · have hr : (⟨0 + (r.val - 0), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 0 + (r.val - 0) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen0 ⟨r.val - 0, by omega⟩
  rcases lt_or_ge r.val 92 with h1 | h1
  · have hr : (⟨46 + (r.val - 46), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 46 + (r.val - 46) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen1 ⟨r.val - 46, by omega⟩
  rcases lt_or_ge r.val 138 with h2 | h2
  · have hr : (⟨92 + (r.val - 92), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 92 + (r.val - 92) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen2 ⟨r.val - 92, by omega⟩
  rcases lt_or_ge r.val 184 with h3 | h3
  · have hr : (⟨138 + (r.val - 138), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 138 + (r.val - 138) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen3 ⟨r.val - 138, by omega⟩
  rcases lt_or_ge r.val 207 with h4 | h4
  · have hr : (⟨184 + (r.val - 184), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 184 + (r.val - 184) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen4a ⟨r.val - 184, by omega⟩
  rcases lt_or_ge r.val 230 with h5 | h5
  · have hr : (⟨207 + (r.val - 207), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 207 + (r.val - 207) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen4b ⟨r.val - 207, by omega⟩
  rcases lt_or_ge r.val 276 with h6 | h6
  · have hr : (⟨230 + (r.val - 230), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 230 + (r.val - 230) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen5 ⟨r.val - 230, by omega⟩
  rcases lt_or_ge r.val 322 with h7 | h7
  · have hr : (⟨276 + (r.val - 276), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 276 + (r.val - 276) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen6 ⟨r.val - 276, by omega⟩
  rcases lt_or_ge r.val 368 with h8 | h8
  · have hr : (⟨322 + (r.val - 322), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 322 + (r.val - 322) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen7 ⟨r.val - 322, by omega⟩
  rcases lt_or_ge r.val 414 with h9 | h9
  · have hr : (⟨368 + (r.val - 368), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 368 + (r.val - 368) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen8 ⟨r.val - 368, by omega⟩
  rcases lt_or_ge r.val 437 with h10 | h10
  · have hr : (⟨414 + (r.val - 414), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 414 + (r.val - 414) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen9a ⟨r.val - 414, by omega⟩
  rcases lt_or_ge r.val 460 with h11 | h11
  · have hr : (⟨437 + (r.val - 437), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 437 + (r.val - 437) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen9b ⟨r.val - 437, by omega⟩
  rcases lt_or_ge r.val 483 with h12 | h12
  · have hr : (⟨460 + (r.val - 460), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 460 + (r.val - 460) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen10a ⟨r.val - 460, by omega⟩
  rcases lt_or_ge r.val 506 with h13 | h13
  · have hr : (⟨483 + (r.val - 483), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 483 + (r.val - 483) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen10b ⟨r.val - 483, by omega⟩
  rcases lt_or_ge r.val 529 with h14 | h14
  · have hr : (⟨506 + (r.val - 506), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 506 + (r.val - 506) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen11a ⟨r.val - 506, by omega⟩
  rcases lt_or_ge r.val 552 with h15 | h15
  · have hr : (⟨529 + (r.val - 529), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 529 + (r.val - 529) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen11b ⟨r.val - 529, by omega⟩
  rcases lt_or_ge r.val 598 with h16 | h16
  · have hr : (⟨552 + (r.val - 552), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 552 + (r.val - 552) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen12 ⟨r.val - 552, by omega⟩
  rcases lt_or_ge r.val 644 with h17 | h17
  · have hr : (⟨598 + (r.val - 598), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 598 + (r.val - 598) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen13 ⟨r.val - 598, by omega⟩
  rcases lt_or_ge r.val 690 with h18 | h18
  · have hr : (⟨644 + (r.val - 644), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 644 + (r.val - 644) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen14 ⟨r.val - 644, by omega⟩
  rcases lt_or_ge r.val 736 with h19 | h19
  · have hr : (⟨690 + (r.val - 690), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 690 + (r.val - 690) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen15 ⟨r.val - 690, by omega⟩
  rcases lt_or_ge r.val 782 with h20 | h20
  · have hr : (⟨736 + (r.val - 736), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 736 + (r.val - 736) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen16 ⟨r.val - 736, by omega⟩
  rcases lt_or_ge r.val 828 with h21 | h21
  · have hr : (⟨782 + (r.val - 782), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 782 + (r.val - 782) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen17 ⟨r.val - 782, by omega⟩
  rcases lt_or_ge r.val 874 with h22 | h22
  · have hr : (⟨828 + (r.val - 828), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 828 + (r.val - 828) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen18 ⟨r.val - 828, by omega⟩
  rcases lt_or_ge r.val 920 with h23 | h23
  · have hr : (⟨874 + (r.val - 874), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 874 + (r.val - 874) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen19 ⟨r.val - 874, by omega⟩
  rcases lt_or_ge r.val 966 with h24 | h24
  · have hr : (⟨920 + (r.val - 920), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 920 + (r.val - 920) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen20 ⟨r.val - 920, by omega⟩
  rcases lt_or_ge r.val 1012 with h25 | h25
  · have hr : (⟨966 + (r.val - 966), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 966 + (r.val - 966) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen21 ⟨r.val - 966, by omega⟩
  rcases lt_or_ge r.val 1058 with h26 | h26
  · have hr : (⟨1012 + (r.val - 1012), by omega⟩ : Fin 1104) = r := by
      apply Fin.ext
      show 1012 + (r.val - 1012) = r.val
      omega
    rw [← hr]
    exact mme_released_recursive_level2_pen22 ⟨r.val - 1012, by omega⟩
  have hr : (⟨1058 + (r.val - 1058), by omega⟩ : Fin 1104) = r := by
    apply Fin.ext
    show 1058 + (r.val - 1058) = r.val
    omega
  rw [← hr]
  exact mme_released_recursive_level2_pen23 ⟨r.val - 1058, by omega⟩

/-- The split distribution used by the penalty, in rational form. -/
theorem alpha_cast (r : Fin 1104) :
    (fun c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r) ↦
      (m2 r c : ℝ) / ((n2 r : ℕ) : ℝ)) =
      fun c ↦ ((alphaQ r c : ℚ) : ℝ) := by
  funext c
  unfold alphaQ
  push_cast
  ring

/-- The whole level-two penalty potential, from the uniform per-region bound. -/
theorem penalty_total (hb : ∀ r : Fin 1104,
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
        qvalQ (fun t ↦ ∑ i, PE r i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
        (alphaQ r c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE r i (c.val i) t)) ≤ 1/(5 * 10^7)) :
    penaltyPotential n2 m2 ≤ (∑ r : Fin 1104, ((n2 r : ℕ) : ℝ)) / (5 * 10^7) := by
  unfold penaltyPotential
  rw [Finset.sum_div]
  refine Finset.sum_le_sum (fun r _ ↦ ?_)
  rw [mul_assoc, alpha_cast r]
  have h1 := pen_bound r
  have h2 : ((( (∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
      qvalQ (fun t ↦ ∑ i, PE r i (c.val i) t)) - 2 +
    ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
      (alphaQ r c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE r i (c.val i) t) : ℚ)) : ℝ) ≤
      ((1/(5 * 10^7) : ℚ) : ℝ) := by
    exact_mod_cast hb r
  have h3 : Real.log 2 * entropyPenalty (fun c ↦ ((alphaQ r c : ℚ) : ℝ)) ≤
      ((1/(5 * 10^7) : ℚ) : ℝ) := le_trans h1 h2
  have hn : (0 : ℝ) ≤ ((n2 r : ℕ) : ℝ) := by positivity
  have : ((1/(5 * 10^7) : ℚ) : ℝ) = 1 / (5 * 10^7) := by norm_num
  rw [this] at h3
  calc ((n2 r : ℕ) : ℝ) * (Real.log 2 * entropyPenalty (fun c ↦ ((alphaQ r c : ℚ) : ℝ)))
      ≤ ((n2 r : ℕ) : ℝ) * (1 / (5 * 10^7)) := by
        exact mul_le_mul_of_nonneg_left h3 hn
    _ = ((n2 r : ℕ) : ℝ) / (5 * 10^7) := by ring

end MME.L2Cert

namespace MME.L2Cert

theorem n2_sum : ∑ r : Fin 1104, n2 r =
    7059480968075670977012057703633505689000000000000000000000000 := by
  decide +kernel

/-- The level-two regional rate, above the published margin constant. -/
theorem level2_rate (hb : ∀ r : Fin 1104,
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
        qvalQ (fun t ↦ ∑ i, PE r i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
        (alphaQ r c) ^ 2 / qvalQ (fun t ↦ ∑ i, PE r i (c.val i) t)) ≤ 1/(5 * 10^7)) :
    ((585967670317 * 6 * 10 ^ 48 : ℕ) : ℝ) < regionalRate htotal2 n2 m2 mu2 := by
  have hpb := mme_released_recursive_level2_parent_bounds
  have hsum : ∑ r : Fin 1104, ((n2 r : ℕ) : ℝ) =
      ((7059480968075670977012057703633505689000000000000000000000000 : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, n2_sum]
  -- the three certified bounds, as reals
  have hY : ((585967670317 * 6 * 10 ^ 48 : ℕ) : ℝ) <
      parentPotential htotal2 n2 m2 (mu2 1) := by
    refine lt_of_lt_of_le ?_ (hpb.1 1)
    rw [hpb.2.2.1]
    norm_num
  have hZ : ((585967670317 * 6 * 10 ^ 48 : ℕ) : ℝ) <
      parentPotential htotal2 n2 m2 (mu2 2) := by
    refine lt_of_lt_of_le ?_ (hpb.1 2)
    rw [hpb.2.2.2]
    norm_num
  have hX : ((585967670317 * 6 * 10 ^ 48 : ℕ) : ℝ) <
      coarsePotential m2 0 - penaltyPotential n2 m2 := by
    have hc : (((3515806618502173629491594525557823285980675975401445058912361661975000000000000000000000000 : ℤ) : ℚ) : ℝ)/10^30 ≤ coarsePotential m2 0 := by
      rw [mme_released_recursive_level2_coarse.2.2.2]
      refine le_trans (le_of_eq ?_) (hpb.1 0)
      rw [hpb.2.1]
    have hp := penalty_total hb
    rw [hsum] at hp
    have : ((585967670317 * 6 * 10 ^ 48 : ℕ) : ℝ) <
        (((3515806618502173629491594525557823285980675975401445058912361661975000000000000000000000000 : ℤ) : ℚ) : ℝ)/10^30 -
        ((7059480968075670977012057703633505689000000000000000000000000 : ℕ) : ℝ) / (5 * 10^7) := by
      push_cast
      norm_num
    exact lt_of_lt_of_le this (sub_le_sub hc hp)
  have hc0 : compatibilityPotential 0 (mu2 1) = 0 := by
    show RegionRealization.potential
      (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (mu2 (yzMode 0))) = 0
    exact mme_released_recursive_level2_structure.1 0
  have hc1 : compatibilityPotential 1 (mu2 2) = 0 := by
    show RegionRealization.potential
      (partCount (yzBoundary 1) (modeGroup (yzMode 1)) (mu2 (yzMode 1))) = 0
    exact mme_released_recursive_level2_structure.1 1
  show _ < min _ (min _ _)
  refine lt_min hX (lt_min ?_ ?_)
  · rw [hc0, sub_zero]
    exact hY
  · rw [hc1, sub_zero]
    exact hZ

end MME.L2Cert

theorem solution :
    ((585967670317 * 6 * 10 ^ 48 : ℕ) : ℝ) < regionalRate htotal2 n2 m2 mu2 :=
  MME.L2Cert.level2_rate MME.L2Cert.pen_all
