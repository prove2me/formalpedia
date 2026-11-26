-- Prove2me | solution 1 for ReweightedNPMLE.radial_localization
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:09:50.079928+00:00
-- url     : https://prove2.me/submissions/460badcf-256f-42de-aaea-e35322758cf4

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import Theorems.Thm_ReweightedNPMLE_log_one_add_sq_le_two_sq
import Theorems.Thm_ReweightedNPMLE_radial_localization_sq

-- Inline helpers preserved from ReweightedNPMLE.Localization.
section
/-!
# Radial localization inequalities

Scalar and coordinatewise estimates used by the radial-localization part of the
effective-dimension theorem.
-/

open scoped BigOperators
open Set

namespace ReweightedNPMLE







theorem sum_log_one_add_sq_le_two_sum_sq {n : ℕ} (u : Fin n → ℝ)
    (hu : ∀ i, |u i| ≤ 1 / 16) :
    ∑ i, Real.log (1 + u i) ^ 2 ≤ 2 * ∑ i, u i ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ log_one_add_sq_le_two_sq (hu i)





end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.RadialLocalization.
section
open scoped BigOperators
open Set

namespace ReweightedNPMLE

theorem abs_le_sqrt_sum_sq {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    |u i| ≤ Real.sqrt (∑ j, u j ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (u j)) (Finset.mem_univ i)





theorem abs_log_one_add_sub_self_le {u : ℝ} (hu : |u| ≤ 1 / 16) :
    |Real.log (1 + u) - u| ≤ (16 / 15 : ℝ) * u ^ 2 := by
  have hu1 : |u| < 1 := lt_of_le_of_lt hu (by norm_num)
  have hseries := Real.abs_log_sub_add_sum_range_le (x := -u) (by simpa) 1
  norm_num [Finset.sum_range_succ] at hseries
  have hden : 0 < 1 - |u| := by positivity
  have hfrac : u ^ 2 / (1 - |u|) ≤ (16 / 15 : ℝ) * u ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg u, abs_nonneg u]
  simpa [sub_eq_add_neg, add_comm] using hseries.trans hfrac













end ReweightedNPMLE
end

open scoped BigOperators
open Set

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {n : ℕ}
    (U : Set (Fin n → ℝ)) (hU : Convex ℝ U) (hzero : (0 : Fin n → ℝ) ∈ U)
    (w u : Fin n → ℝ) (huU : u ∈ U) (hupos : ∀ i, 0 < 1 + u i)
    (A E τ : ℝ) (hE0 : 0 ≤ E) (hτ0 : 0 ≤ τ)
    (hw : ∀ i, |w i - 1| ≤ 1 / 16)
    (hA : A ≤ (1 / 16 : ℝ) / 24)
    (hE : E ≤ (1 / 16 : ℝ) ^ 2 / 24)
    (hfirst : ∀ v ∈ U, ∑ i, v i ≤ 0)
    (hpair : ∀ v ∈ U, ∑ i, (w i - 1) * v i ≤
      A * Real.sqrt (∑ i, v i ^ 2) + E)
    (hτ : τ < (1 / 16 : ℝ) ^ 2 / 12)
    (hnear : -τ ≤ ∑ i, w i * Real.log (1 + u i)) :
    Real.sqrt (∑ i, u i ^ 2) < 1 / 16 ∧
      ∑ i, u i ^ 2 ≤ 36 * A ^ 2 + 12 * E + 12 * τ ∧
      0 ≤ -(∑ i, Real.log (1 + u i)) ∧
      -(∑ i, Real.log (1 + u i)) ≤
        37 * A ^ 2 + 13 * E + 13 * τ ∧
      ∑ i, Real.log (1 + u i) ^ 2 ≤
        72 * A ^ 2 + 24 * E + 24 * τ ∧
      ∑ i, (w i - 1) * Real.log (1 + u i) ≤
        37 * A ^ 2 + 13 * E + 12 * τ := by
  obtain ⟨hlocal, hsq⟩ := radial_localization_sq U hU hzero w u huU hupos
    A E τ hτ0 hw hA hE hfirst hpair hτ hnear
  let x : ℝ := Real.sqrt (∑ i, u i ^ 2)
  have hsumSq0 : 0 ≤ ∑ i, u i ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg (u i)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxSq : x ^ 2 = ∑ i, u i ^ 2 := Real.sq_sqrt hsumSq0
  have hu16 : ∀ i, |u i| ≤ 1 / 16 := by
    intro i
    exact (abs_le_sqrt_sum_sq u i).trans hlocal.le
  have hlogsum : ∑ i, Real.log (1 + u i) ≤ 0 := by
    calc
      ∑ i, Real.log (1 + u i) ≤ ∑ i, u i := by
        apply Finset.sum_le_sum
        intro i _
        simpa using Real.log_le_sub_one_of_pos (hupos i)
      _ ≤ 0 := hfirst u huU
  have hpairlogIdentity :
      ∑ i, (w i - 1) * Real.log (1 + u i) =
        (∑ i, (w i - 1) * u i) +
          ∑ i, (w i - 1) * (Real.log (1 + u i) - u i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrem : ∑ i, (w i - 1) * (Real.log (1 + u i) - u i) ≤
      (1 / 15 : ℝ) * ∑ i, u i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      (w i - 1) * (Real.log (1 + u i) - u i) ≤
          |w i - 1| * |Real.log (1 + u i) - u i| := by
        rw [← abs_mul]
        exact le_abs_self _
      _ ≤ (1 / 16 : ℝ) * |Real.log (1 + u i) - u i| :=
        mul_le_mul_of_nonneg_right (hw i) (abs_nonneg _)
      _ ≤ (1 / 16 : ℝ) * ((16 / 15 : ℝ) * u i ^ 2) :=
        mul_le_mul_of_nonneg_left
          (abs_log_one_add_sub_self_le (hu16 i)) (by norm_num)
      _ = (1 / 15 : ℝ) * u i ^ 2 := by ring
  have hpairlogRaw : ∑ i, (w i - 1) * Real.log (1 + u i) ≤
      A * x + E + (1 / 15 : ℝ) * x ^ 2 := by
    rw [hpairlogIdentity]
    change (∑ i, (w i - 1) * u i) +
        ∑ i, (w i - 1) * (Real.log (1 + u i) - u i) ≤ _
    have hp := hpair u huU
    change (∑ i, (w i - 1) * u i) ≤ A * x + E at hp
    rw [hxSq]
    linarith
  have hpairlog : ∑ i, (w i - 1) * Real.log (1 + u i) ≤
      37 * A ^ 2 + 13 * E + 12 * τ := by
    have hsq' : x ^ 2 ≤ 36 * A ^ 2 + 12 * E + 12 * τ := by
      rw [hxSq]
      exact hsq
    nlinarith [sq_nonneg (x - 36 * A)]
  have hloss : -(∑ i, Real.log (1 + u i)) ≤
      37 * A ^ 2 + 13 * E + 13 * τ := by
    have hdecomp : ∑ i, w i * Real.log (1 + u i) =
        (∑ i, Real.log (1 + u i)) +
          ∑ i, (w i - 1) * Real.log (1 + u i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hdecomp] at hnear
    linarith
  have hlogSq := sum_log_one_add_sq_le_two_sum_sq u hu16
  refine ⟨hlocal, hsq, by linarith, hloss, ?_, hpairlog⟩
  calc
    ∑ i, Real.log (1 + u i) ^ 2 ≤ 2 * ∑ i, u i ^ 2 := hlogSq
    _ ≤ 72 * A ^ 2 + 24 * E + 24 * τ := by linarith
