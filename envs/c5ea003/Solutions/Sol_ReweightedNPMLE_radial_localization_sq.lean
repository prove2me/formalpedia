-- Prove2me | solution 1 for ReweightedNPMLE.radial_localization_sq
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:09:04.89437+00:00
-- url     : https://prove2.me/submissions/327b19a9-cf22-4667-9a28-4f135304b4fa

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import Theorems.Thm_ReweightedNPMLE_log_one_add_le_sub_sq_third

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

/-- The quadratic completion at the heart of Lemma 7.4. -/
theorem radial_quadratic_bound {x A E τ : ℝ}
    (h : x ^ 2 ≤ 6 * (A * x + E + τ)) :
    x ^ 2 ≤ 36 * A ^ 2 + 12 * E + 12 * τ := by
  nlinarith [sq_nonneg (x - 6 * A)]











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







theorem log_one_add_smul_ge {u a : ℝ} (hu : 0 < 1 + u)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    a * Real.log (1 + u) ≤ Real.log (1 + a * u) := by
  have hconc := strictConcaveOn_log_Ioi.concaveOn
  have h := hconc.2 hu (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    ha0 (sub_nonneg.mpr ha1)
    (by ring : a + (1 - a) = 1)
  calc
    a * Real.log (1 + u) ≤
        Real.log (a * (1 + u) + (1 - a) * 1) := by
      simpa [smul_eq_mul] using h
    _ = Real.log (1 + a * u) := by congr 1 <;> ring

theorem radial_objective_upper {n : ℕ}
    (w u : Fin n → ℝ) (A E : ℝ)
    (hw : ∀ i, |w i - 1| ≤ 1 / 16)
    (hu : ∀ i, |u i| ≤ 1 / 4)
    (hfirst : ∑ i, u i ≤ 0)
    (hpair : ∑ i, (w i - 1) * u i ≤
      A * Real.sqrt (∑ i, u i ^ 2) + E) :
    ∑ i, w i * Real.log (1 + u i) ≤
      A * Real.sqrt (∑ i, u i ^ 2) + E -
        (1 / 6 : ℝ) * ∑ i, u i ^ 2 := by
  have hwpos (i : Fin n) : 0 ≤ w i := by
    have hi := neg_le_of_abs_le (hw i)
    linarith
  calc
    ∑ i, w i * Real.log (1 + u i) ≤
        ∑ i, w i * (u i - u i ^ 2 / 3) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (log_one_add_le_sub_sq_third (hu i)) (hwpos i)
    _ = ∑ i, (u i + (w i - 1) * u i - w i * u i ^ 2 / 3) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, u i) + (∑ i, (w i - 1) * u i) -
        ∑ i, w i * u i ^ 2 / 3 := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ ≤ (∑ i, (w i - 1) * u i) -
        (1 / 6 : ℝ) * ∑ i, u i ^ 2 := by
      have hsquare : (1 / 6 : ℝ) * ∑ i, u i ^ 2 ≤
          ∑ i, w i * u i ^ 2 / 3 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        have hi := neg_le_of_abs_le (hw i)
        have hs := sq_nonneg (u i)
        nlinarith
      linarith
    _ ≤ A * Real.sqrt (∑ i, u i ^ 2) + E -
        (1 / 6 : ℝ) * ∑ i, u i ^ 2 := by linarith









end ReweightedNPMLE
end

open scoped BigOperators
open Set

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {n : ℕ}
    (U : Set (Fin n → ℝ)) (hU : Convex ℝ U) (hzero : (0 : Fin n → ℝ) ∈ U)
    (w u : Fin n → ℝ) (huU : u ∈ U) (hupos : ∀ i, 0 < 1 + u i)
    (A E τ : ℝ) (hτ0 : 0 ≤ τ)
    (hw : ∀ i, |w i - 1| ≤ 1 / 16)
    (hA : A ≤ (1 / 16 : ℝ) / 24)
    (hE : E ≤ (1 / 16 : ℝ) ^ 2 / 24)
    (hfirst : ∀ v ∈ U, ∑ i, v i ≤ 0)
    (hpair : ∀ v ∈ U, ∑ i, (w i - 1) * v i ≤
      A * Real.sqrt (∑ i, v i ^ 2) + E)
    (hτ : τ < (1 / 16 : ℝ) ^ 2 / 12)
    (hnear : -τ ≤ ∑ i, w i * Real.log (1 + u i)) :
    Real.sqrt (∑ i, u i ^ 2) < 1 / 16 ∧
      ∑ i, u i ^ 2 ≤ 36 * A ^ 2 + 12 * E + 12 * τ := by
  let x : ℝ := Real.sqrt (∑ i, u i ^ 2)
  have hsq : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg (u i)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxSq : x ^ 2 = ∑ i, u i ^ 2 := Real.sq_sqrt hsq
  have hlocal : x < 1 / 16 := by
    by_contra hn
    have hρx : (1 / 16 : ℝ) ≤ x := le_of_not_gt hn
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hρx
    let a : ℝ := (1 / 16 : ℝ) / x
    let q : Fin n → ℝ := a • u
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have ha1 : a ≤ 1 := by
      dsimp [a]
      rw [div_le_one hxpos]
      exact hρx
    have hqU : q ∈ U := by
      have hc := hU hzero huU (sub_nonneg.mpr ha1) ha0
        (by ring : (1 - a) + a = 1)
      simpa [q] using hc
    have hqSq : ∑ i, q i ^ 2 = (1 / 16 : ℝ) ^ 2 := by
      calc
        ∑ i, q i ^ 2 = a ^ 2 * ∑ i, u i ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp [q]
          ring
        _ = a ^ 2 * x ^ 2 := by rw [hxSq]
        _ = (1 / 16 : ℝ) ^ 2 := by
          dsimp [a]
          field_simp
    have hqNorm : Real.sqrt (∑ i, q i ^ 2) = (1 / 16 : ℝ) := by
      rw [hqSq, Real.sqrt_sq]
      norm_num
    have hqabs : ∀ i, |q i| ≤ 1 / 4 := by
      intro i
      exact (abs_le_sqrt_sum_sq q i).trans (by rw [hqNorm]; norm_num)
    have hupper := radial_objective_upper w q A E hw hqabs
      (hfirst q hqU) (hpair q hqU)
    rw [hqNorm, hqSq] at hupper
    have hupper' : ∑ i, w i * Real.log (1 + q i) ≤
        -((1 / 16 : ℝ) ^ 2 / 12) := by
      calc
        ∑ i, w i * Real.log (1 + q i) ≤
            A * (1 / 16 : ℝ) + E - (1 / 6 : ℝ) * (1 / 16 : ℝ) ^ 2 := hupper
        _ ≤ -((1 / 16 : ℝ) ^ 2 / 12) := by nlinarith
    have hw0 (i : Fin n) : 0 ≤ w i := by
      have hi := neg_le_of_abs_le (hw i)
      linarith
    have hscale : a * (∑ i, w i * Real.log (1 + u i)) ≤
        ∑ i, w i * Real.log (1 + q i) := by
      calc
        a * (∑ i, w i * Real.log (1 + u i)) =
            ∑ i, w i * (a * Real.log (1 + u i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ ∑ i, w i * Real.log (1 + a * u i) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left
            (log_one_add_smul_ge (hupos i) ha0 ha1) (hw0 i)
        _ = ∑ i, w i * Real.log (1 + q i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [q]
    have hlower : -τ ≤ ∑ i, w i * Real.log (1 + q i) := by
      calc
        -τ ≤ a * (-τ) := by nlinarith
        _ ≤ a * (∑ i, w i * Real.log (1 + u i)) :=
          mul_le_mul_of_nonneg_left hnear ha0
        _ ≤ _ := hscale
    linarith
  have huabs : ∀ i, |u i| ≤ 1 / 4 := by
    intro i
    exact (abs_le_sqrt_sum_sq u i).trans
      (by dsimp [x] at hlocal; exact hlocal.le.trans (by norm_num))
  have hupper := radial_objective_upper w u A E hw huabs
    (hfirst u huU) (hpair u huU)
  change x < 1 / 16 at hlocal
  change (∑ i, w i * Real.log (1 + u i)) ≤
    A * x + E - (1 / 6 : ℝ) * (∑ i, u i ^ 2) at hupper
  have hquad : x ^ 2 ≤ 6 * (A * x + E + τ) := by
    rw [hxSq]
    linarith
  have hbound := radial_quadratic_bound hquad
  rw [hxSq] at hbound
  exact ⟨by simpa [x] using hlocal, hbound⟩
