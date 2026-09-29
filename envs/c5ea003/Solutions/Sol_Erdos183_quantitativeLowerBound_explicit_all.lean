-- Prove2me | solution 1 for Erdos183.quantitativeLowerBound_explicit_all
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:33:00.907059+00:00
-- url     : https://prove2.me/submissions/88725737-fbe1-4a5f-903c-e85bd29c8db3

import Definitions.Def_erdos183_core
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Data.Real.StarOrdered
import Theorems.Thm_Erdos183_allColourPaletteRamsey_exponential_bound_sharp
import Theorems.Thm_Erdos183_one_le_log_nat_of_three_le
import Theorems.Thm_Erdos183_paletteColourCount_three
import Theorems.Thm_Erdos183_paletteLogWidth_le_two_log
import Theorems.Thm_Erdos183_triangleFree_lt_triangleRamseyNumber
import Theorems.Thm_Erdos183_two_mul_stage_le_paletteColourCount

open Filter Finset SimpleGraph
open scoped Topology

namespace Erdos183

theorem paletteColourCount_le_twenty_six_sharp (H : ℕ) (hH : 3 ≤ H) :
    (paletteColourCount H : ℝ) ≤
      26 * (H : ℝ) ^ 3 * Real.log (H : ℝ) ^ 3 := by
  let y : ℝ := (H : ℝ) * Real.log (H : ℝ)
  have hlog : 1 ≤ Real.log (H : ℝ) :=
    one_le_log_nat_of_three_le H hH
  have hHreal : (1 : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast (show 1 ≤ H by omega)
  have hy : 1 ≤ y := by
    dsimp [y]
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (H : ℝ) * Real.log (H : ℝ) := by gcongr
  have harg : 0 ≤ 2 * (H : ℝ) * Real.log (H : ℝ) := by
    positivity
  have hceil :
      (⌈2 * (H : ℝ) * Real.log (H : ℝ)⌉₊ : ℝ) ≤
        2 * (H : ℝ) * Real.log (H : ℝ) + 1 :=
    (Nat.ceil_lt_add_one harg).le
  have hm : (saturatedMatrixWidth H : ℝ) ≤ 3 * y := by
    unfold saturatedMatrixWidth
    dsimp [y]
    nlinarith
  have hmsucc : (saturatedMatrixWidth H : ℝ) + 1 ≤ 4 * y := by
    linarith
  have hone : (1 : ℝ) ≤ y ^ 2 := by
    nlinarith [sq_nonneg (y - 1)]
  have hrows : (saturatedMatrixRows H : ℝ) ≤ 13 * y ^ 2 := by
    unfold saturatedMatrixRows
    push_cast
    calc
      (saturatedMatrixWidth H : ℝ) *
          ((saturatedMatrixWidth H : ℝ) + 1) + 1 ≤
        (3 * y) * (4 * y) + y ^ 2 := by
          gcongr
      _ = 13 * y ^ 2 := by ring
  have hwidth := paletteLogWidth_le_two_log H hH
  unfold paletteColourCount
  push_cast
  calc
    (H : ℝ) *
        ((paletteLogWidth H : ℝ) * (saturatedMatrixRows H : ℝ)) ≤
      (H : ℝ) *
        ((2 * Real.log (H : ℝ)) * (13 * y ^ 2)) := by
          gcongr
    _ = 26 * (H : ℝ) ^ 3 * Real.log (H : ℝ) ^ 3 := by
      dsimp [y]
      ring

theorem paletteStage_cube_root_control_six_sharp (H k : ℕ)
    (hH : 3 ≤ H)
    (hlower : paletteColourCount H ≤ k)
    (hupper : k < paletteColourCount (H + 1)) :
    (k : ℝ) ^ ((1 : ℝ) / 3) ≤
      6 * (H : ℝ) * Real.log (k : ℝ) := by
  have hkstage : 2 * H ≤ k :=
    (two_mul_stage_le_paletteColourCount H).trans hlower
  have hHk : H + 1 ≤ k := by omega
  have hkthree : 3 ≤ k := by omega
  have hlogk : 1 ≤ Real.log (k : ℝ) :=
    one_le_log_nat_of_three_le k hkthree
  have hlognext :
      Real.log ((H + 1 : ℕ) : ℝ) ≤ Real.log (k : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hHk
  have hHnext : ((H + 1 : ℕ) : ℝ) ≤ 2 * (H : ℝ) := by
    exact_mod_cast (show H + 1 ≤ 2 * H by omega)
  have hkbound :
      (k : ℝ) ≤
        26 * (((H + 1 : ℕ) : ℝ)) ^ 3 *
          Real.log ((H + 1 : ℕ) : ℝ) ^ 3 := by
    calc
      (k : ℝ) ≤ (paletteColourCount (H + 1) : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hupper)
      _ ≤ 26 * (((H + 1 : ℕ) : ℝ)) ^ 3 *
          Real.log ((H + 1 : ℕ) : ℝ) ^ 3 :=
        paletteColourCount_le_twenty_six_sharp (H + 1) (by omega)
  have hcube :
      (k : ℝ) ≤ (6 * (H : ℝ) * Real.log (k : ℝ)) ^ 3 := by
    calc
      (k : ℝ) ≤
          26 * (((H + 1 : ℕ) : ℝ)) ^ 3 *
            Real.log ((H + 1 : ℕ) : ℝ) ^ 3 := hkbound
      _ ≤ 26 * (2 * (H : ℝ)) ^ 3 * Real.log (k : ℝ) ^ 3 := by
        gcongr
      _ = 208 * (H : ℝ) ^ 3 * Real.log (k : ℝ) ^ 3 := by
        ring
      _ ≤ 216 * (H : ℝ) ^ 3 * Real.log (k : ℝ) ^ 3 := by
        gcongr
        norm_num
      _ = (6 * (H : ℝ) * Real.log (k : ℝ)) ^ 3 := by
        ring
  have hrootcube :
      ((k : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = (k : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  apply (pow_le_pow_iff_left₀
    (Real.rpow_nonneg (by positivity) _)
    (by positivity)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [hrootcube]
  exact hcube

theorem quantitativeLowerBound_explicit_small (k : ℕ)
    (hk : 2 ≤ k) (hsmall : k < 342) :
    (((1 : ℝ) / (6 * Real.exp 38)) *
      (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
        (triangleRamseyNumber k : ℝ) := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log (k : ℝ) := by
    calc
      (1 / 2 : ℝ) ≤ Real.log 2 := by
        nlinarith [Real.log_two_gt_d9]
      _ ≤ Real.log (k : ℝ) := by
        apply Real.log_le_log (by norm_num)
        exact_mod_cast hk
  have hroot : (k : ℝ) ^ ((1 : ℝ) / 3) ≤ (7 : ℝ) := by
    apply (pow_le_pow_iff_left₀
      (Real.rpow_nonneg (by positivity) _) (by positivity)
      (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    exact_mod_cast (show k ≤ 343 by omega)
  have hexp : (39 : ℝ) ≤ Real.exp 38 := by
    nlinarith [Real.add_one_le_exp (38 : ℝ)]
  have hbase :
      ((1 : ℝ) / (6 * Real.exp 38)) *
        (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ) ≤ 1 := by
    apply (div_le_one (by linarith : 0 < Real.log (k : ℝ))).mpr
    calc
      ((1 : ℝ) / (6 * Real.exp 38)) *
          (k : ℝ) ^ ((1 : ℝ) / 3) ≤
          (1 / (6 * (39 : ℝ))) * 7 := by gcongr
      _ ≤ Real.log (k : ℝ) := by norm_num; linarith
  calc
    (((1 : ℝ) / (6 * Real.exp 38)) *
        (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
        (1 : ℝ) ^ k := by gcongr
    _ = 1 := one_pow _
    _ ≤ (triangleRamseyNumber k : ℝ) := by
      let C : SimpleGraph.TopEdgeLabeling (Fin 0) (Fin k) :=
        fun _ => ⟨0, by omega⟩
      exact_mod_cast triangleFree_lt_triangleRamseyNumber C
        (fun _ => SimpleGraph.cliqueFree_of_card_lt (by simp))

end Erdos183

open Erdos183

theorem solution :
    ∀ k : ℕ, 2 ≤ k →
      (((1 : ℝ) / (6 * Real.exp 38)) *
        (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
          (triangleRamseyNumber k : ℝ) := by
  intro k hk
  by_cases hlarge : paletteColourCount 3 ≤ k
  · obtain ⟨H, hH, hlower, hupper, hramsey⟩ :=
      allColourPaletteRamsey_exponential_bound_sharp k hlarge
    have hkthree : 3 ≤ k := by
      have hstage := (two_mul_stage_le_paletteColourCount H).trans hlower
      omega
    have hlog : 0 < Real.log (k : ℝ) := by
      have hone := one_le_log_nat_of_three_le k hkthree
      linarith
    have hroot :=
      paletteStage_cube_root_control_six_sharp H k hH hlower hupper
    have hbase :
        ((1 : ℝ) / (6 * Real.exp 38)) *
            (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ) ≤
          (H : ℝ) / Real.exp 38 := by
      calc
        ((1 : ℝ) / (6 * Real.exp 38)) *
            (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ) =
          (k : ℝ) ^ ((1 : ℝ) / 3) /
            (6 * Real.log (k : ℝ) * Real.exp 38) := by
          field_simp
        _ ≤ (H : ℝ) / Real.exp 38 := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith [mul_le_mul_of_nonneg_right hroot
            (Real.exp_pos 38).le]
    calc
      (((1 : ℝ) / (6 * Real.exp 38)) *
          (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
        ((H : ℝ) / Real.exp 38) ^ k := by gcongr
      _ ≤ (triangleRamseyNumber k : ℝ) := hramsey
  · apply quantitativeLowerBound_explicit_small k hk
    rw [paletteColourCount_three] at hlarge
    omega
