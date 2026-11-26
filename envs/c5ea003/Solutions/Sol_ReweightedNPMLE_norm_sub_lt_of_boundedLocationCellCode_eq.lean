-- Prove2me | solution 1 for ReweightedNPMLE.norm_sub_lt_of_boundedLocationCellCode_eq
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:05:36.767523+00:00
-- url     : https://prove2.me/submissions/f038deff-e5f9-41ff-a64b-f22edcf3af76

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
import Definitions.Def_ReweightedNPMLE_Gaussian

-- Inline helpers preserved from ReweightedNPMLE.EuclideanLocationNet.
section
/-!
# Explicit finite nets for bounded Euclidean sets

This module implements the coordinate-cell construction used in the paper's
entropy argument.  A set contained in the radius-`S` Euclidean ball is split
into cells of coordinate width `ε / (d + 2)`.  Choosing one point of the set
from each occupied cell gives an internal `ε`-net with an explicit cardinality
bound.
-/

open scoped BigOperators

namespace ReweightedNPMLE









theorem boundedLocation_scaled_coord_nonneg {d : ℕ} {S ε : ℝ}
    (hε : 0 < ε) (u : Point d) (hu : ‖u‖ ≤ S) (i : Fin d) :
    0 ≤ (u i + S) / boundedLocationCellWidth d ε := by
  have hi := (abs_coord_le_norm u i).trans hu
  have hlo : -S ≤ u i := neg_le_of_abs_le hi
  exact div_nonneg (by linarith) (boundedLocationCellWidth_pos d hε).le



















end ReweightedNPMLE
end

/-!
# Explicit finite nets for bounded Euclidean sets

This module implements the coordinate-cell construction used in the paper's
entropy argument.  A set contained in the radius-`S` Euclidean ball is split
into cells of coordinate width `ε / (d + 2)`.  Choosing one point of the set
from each occupied cell gives an internal `ε`-net with an explicit cardinality
bound.
-/

open scoped BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Points with the same coordinate-cell code are strictly closer than `ε`. -/
theorem solution
    {d : ℕ} {K : Set (Point d)} {S ε : ℝ} (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (u v : K)
    (hcode : boundedLocationCellCode S ε hε hKbound u =
      boundedLocationCellCode S ε hε hKbound v) :
    ‖(u : Point d) - (v : Point d)‖ < ε := by
  have hcoord : ∀ i : Fin d,
      |((u : Point d) - (v : Point d)) i| <
        boundedLocationCellWidth d ε := by
    intro i
    change |(u : Point d) i - (v : Point d) i| <
      boundedLocationCellWidth d ε
    have hfloorNat :
        Nat.floor ((((u : Point d) i + S) /
            boundedLocationCellWidth d ε)) =
          Nat.floor ((((v : Point d) i + S) /
            boundedLocationCellWidth d ε)) := by
      exact Fin.ext_iff.mp (congrFun hcode i)
    have hu0 := boundedLocation_scaled_coord_nonneg hε (u : Point d)
      (hKbound u u.property) i
    have hv0 := boundedLocation_scaled_coord_nonneg hε (v : Point d)
      (hKbound v v.property) i
    have hfloorInt :
        ⌊(((u : Point d) i + S) / boundedLocationCellWidth d ε)⌋ =
          ⌊(((v : Point d) i + S) / boundedLocationCellWidth d ε)⌋ := by
      rw [← Int.natCast_floor_eq_floor hu0,
        ← Int.natCast_floor_eq_floor hv0]
      exact_mod_cast hfloorNat
    have hscaled := Int.abs_sub_lt_one_of_floor_eq_floor hfloorInt
    have hwpos := boundedLocationCellWidth_pos d hε
    have heq :
        ((u : Point d) i + S) / boundedLocationCellWidth d ε -
            ((v : Point d) i + S) / boundedLocationCellWidth d ε =
          ((u : Point d) i - (v : Point d) i) /
            boundedLocationCellWidth d ε := by
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos hwpos, div_lt_one hwpos] at hscaled
    exact hscaled
  have hsum :
      ∑ i : Fin d, (((u : Point d) - (v : Point d)) i) ^ 2 ≤
        ∑ _i : Fin d, (boundedLocationCellWidth d ε) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have hi := (sq_le_sq₀ (abs_nonneg _)
      (boundedLocationCellWidth_pos d hε).le).2 (hcoord i).le
    simpa only [sq_abs] using hi
  have hnormsq : ‖(u : Point d) - (v : Point d)‖ ^ 2 ≤
      (d : ℝ) * (boundedLocationCellWidth d ε) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa using hsum
  have hnorm : ‖(u : Point d) - (v : Point d)‖ ≤
      Real.sqrt d * boundedLocationCellWidth d ε := by
    have hsqrt0 : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    have hsqrtd : (Real.sqrt (d : ℝ)) ^ 2 = d :=
      Real.sq_sqrt (Nat.cast_nonneg d)
    have hrhs : 0 ≤ Real.sqrt d * boundedLocationCellWidth d ε :=
      mul_nonneg hsqrt0 (boundedLocationCellWidth_pos d hε).le
    apply (sq_le_sq₀ (norm_nonneg _) hrhs).1
    rw [mul_pow, hsqrtd]
    exact hnormsq
  have hsqrt : Real.sqrt d < (d : ℝ) + 2 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg d),
      Real.sqrt_nonneg (d : ℝ)]
  have hw : Real.sqrt d * boundedLocationCellWidth d ε < ε := by
    unfold boundedLocationCellWidth
    have hd : (0 : ℝ) < (d : ℝ) + 2 := by positivity
    calc
      Real.sqrt d * (ε / ((d : ℝ) + 2)) <
          ((d : ℝ) + 2) * (ε / ((d : ℝ) + 2)) := by
        gcongr
      _ = ε := by field_simp
  exact hnorm.trans_lt hw
