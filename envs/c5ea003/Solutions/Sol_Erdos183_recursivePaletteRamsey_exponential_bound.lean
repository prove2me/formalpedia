-- Prove2me | solution 1 for Erdos183.recursivePaletteRamsey_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:25:54.261085+00:00
-- url     : https://prove2.me/submissions/6feedfbd-cfed-44a0-ae1c-76bdc8317b38

import Definitions.Def_erdos183_core
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Theorems.Thm_Erdos183_exists_recursivePaletteStage
import Theorems.Thm_Erdos183_factorial_exp_lower
import Theorems.Thm_Erdos183_triangleFree_lt_triangleRamseyNumber

open Filter Finset SimpleGraph
open scoped Topology

namespace Erdos183

theorem palette_exp_loss_bound (H a s : ℕ)
    (hH : 2 ≤ H) (ha : 2 ≤ a) (hs : 0 < s)
    (hlogH : Real.log (H : ℝ) ≤ (a : ℝ)) :
    ((H : ℝ) / Real.exp 4) ^ (H * (a * s)) ≤
      ((H : ℝ) / Real.exp 1) ^ (H * ((a - 1) * s)) /
        ((s : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * H)) := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hapos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hepos : 0 < Real.exp 1 ^ 2 * (a : ℝ) ^ 2 := by positivity
  have hbasepos : 0 < (H : ℝ) / Real.exp 1 := by positivity
  have htargetpos :
      0 < ((H : ℝ) / Real.exp 4) ^ (H * (a * s)) := by positivity
  have hsourcepos :
      0 < ((H : ℝ) / Real.exp 1) ^ (H * ((a - 1) * s)) /
        ((s : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * H)) := by
    positivity
  have hloga : Real.log (a : ℝ) ≤ (a : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hapos
  have hlogs : Real.log (s : ℝ) ≤ (s : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hspos
  have hweightedH :
      (s : ℝ) * Real.log (H : ℝ) ≤ (s : ℝ) * (a : ℝ) :=
    mul_le_mul_of_nonneg_left hlogH hspos.le
  have hweightedA :
      2 * (s : ℝ) * Real.log (a : ℝ) ≤
        2 * (s : ℝ) * ((a : ℝ) - 1) := by
    gcongr
  have hcore :
      (a : ℝ) * (s : ℝ) * (Real.log (H : ℝ) - 4) +
          Real.log (s : ℝ) +
          (s : ℝ) * (2 + 2 * Real.log (a : ℝ)) ≤
        ((a : ℝ) - 1) * (s : ℝ) *
          (Real.log (H : ℝ) - 1) := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hcore hHpos.le
  have htargetlog :
      Real.log (((H : ℝ) / Real.exp 4) ^ (H * (a * s))) =
        (H : ℝ) * (a : ℝ) * (s : ℝ) *
          (Real.log (H : ℝ) - 4) := by
    rw [Real.log_pow,
      Real.log_div hHpos.ne' (Real.exp_ne_zero 4), Real.log_exp]
    push_cast
    ring
  have hsourcelog :
      Real.log
          (((H : ℝ) / Real.exp 1) ^ (H * ((a - 1) * s)) /
            ((s : ℝ) ^ H *
              (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * H))) =
        (H : ℝ) * ((a : ℝ) - 1) * (s : ℝ) *
            (Real.log (H : ℝ) - 1) -
          ((H : ℝ) * Real.log (s : ℝ) +
            (s : ℝ) * (H : ℝ) *
              (2 + 2 * Real.log (a : ℝ))) := by
    rw [Real.log_div
      (pow_ne_zero _ hbasepos.ne')
      (mul_ne_zero (pow_ne_zero _ hspos.ne') (pow_ne_zero _ hepos.ne'))]
    rw [Real.log_pow,
      Real.log_div hHpos.ne' (Real.exp_ne_zero 1), Real.log_exp]
    rw [Real.log_mul (pow_ne_zero _ hspos.ne') (pow_ne_zero _ hepos.ne'),
      Real.log_pow, Real.log_pow]
    rw [Real.log_mul (pow_ne_zero _ (Real.exp_ne_zero 1))
      (pow_ne_zero _ hapos.ne'), Real.log_pow, Real.log_exp, Real.log_pow]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    ring
  apply (Real.log_le_log_iff htargetpos hsourcepos).mp
  rw [htargetlog, hsourcelog]
  nlinarith

end Erdos183

open Erdos183

theorem solution (H a : ℕ)
    (hH : 2 ≤ H) (ha : 2 ≤ a)
    (hloga : Real.log (H : ℝ) ≤ (a : ℝ)) :
    ((H : ℝ) / Real.exp 4) ^
        (H * (a * saturatedMatrixRows H)) ≤
      (triangleRamseyNumber
        (H * (a * saturatedMatrixRows H)) : ℝ) := by
  obtain ⟨n, C, htriangle, _, hgrowth⟩ :=
    exists_recursivePaletteStage H a H hH ha le_rfl
  have hramsey := triangleFree_lt_triangleRamseyNumber C htriangle
  have hs : 0 < saturatedMatrixRows H := by
    simp [saturatedMatrixRows]
  have hden :
      0 < (saturatedMatrixRows H : ℝ) ^ H *
        (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
          (saturatedMatrixRows H * H) := by
    positivity
  have hsplit :
      a * saturatedMatrixRows H =
        (a - 1) * saturatedMatrixRows H + saturatedMatrixRows H := by
    calc
      a * saturatedMatrixRows H =
          ((a - 1) + 1) * saturatedMatrixRows H := by
        rw [Nat.sub_add_cancel (by omega)]
      _ = (a - 1) * saturatedMatrixRows H + saturatedMatrixRows H := by
        simp [Nat.add_mul]
  unfold PaletteGrowthBound at hgrowth
  nth_rewrite 1 [hsplit] at hgrowth
  rw [pow_add] at hgrowth
  have hfactor : 0 < (H.factorial : ℝ) ^ saturatedMatrixRows H := by
    positivity
  have hcancel :
      (H.factorial : ℝ) ^ ((a - 1) * saturatedMatrixRows H) ≤
        (triangleRamseyNumber (H * (a * saturatedMatrixRows H)) : ℝ) *
          (saturatedMatrixRows H : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
            (saturatedMatrixRows H * H) := by
    apply le_of_mul_le_mul_right ?_ hfactor
    calc
      (H.factorial : ℝ) ^ ((a - 1) * saturatedMatrixRows H) *
          (H.factorial : ℝ) ^ saturatedMatrixRows H ≤
        (n : ℝ) * (saturatedMatrixRows H : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
            (saturatedMatrixRows H * H) *
          (H.factorial : ℝ) ^ saturatedMatrixRows H := hgrowth
      _ ≤ (triangleRamseyNumber
            (H * (a * saturatedMatrixRows H)) : ℝ) *
          (saturatedMatrixRows H : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
            (saturatedMatrixRows H * H) *
          (H.factorial : ℝ) ^ saturatedMatrixRows H := by
        gcongr
  calc
    ((H : ℝ) / Real.exp 4) ^
        (H * (a * saturatedMatrixRows H)) ≤
      ((H : ℝ) / Real.exp 1) ^
          (H * ((a - 1) * saturatedMatrixRows H)) /
        ((saturatedMatrixRows H : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
            (saturatedMatrixRows H * H)) :=
      palette_exp_loss_bound H a (saturatedMatrixRows H)
        hH ha hs hloga
    _ ≤ (triangleRamseyNumber
        (H * (a * saturatedMatrixRows H)) : ℝ) := by
      apply (div_le_iff₀ hden).mpr
      calc
        ((H : ℝ) / Real.exp 1) ^
            (H * ((a - 1) * saturatedMatrixRows H)) =
          (((H : ℝ) / Real.exp 1) ^ H) ^
            ((a - 1) * saturatedMatrixRows H) := by
          rw [pow_mul]
        _ ≤ (H.factorial : ℝ) ^
            ((a - 1) * saturatedMatrixRows H) := by
          gcongr
          exact factorial_exp_lower H (by omega)
        _ ≤ (triangleRamseyNumber
              (H * (a * saturatedMatrixRows H)) : ℝ) *
            ((saturatedMatrixRows H : ℝ) ^ H *
              (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
                (saturatedMatrixRows H * H)) := by
          simpa [mul_assoc] using hcancel
