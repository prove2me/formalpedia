-- Prove2me | solution 1 for ReweightedNPMLE.fittedValue_lipschitzOn
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:00:27.968923+00:00
-- url     : https://prove2.me/submissions/0c97d32d-8bcd-4615-83b6-c46445eb6f4c

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_fitted_maximizer_firstOrder_nonpos

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



















end ReweightedNPMLE
end

/-!
# Regularity of the fitted-value problem

This file proves the analytic regularity part of the paper's effective-dimension
argument.  Variational inequalities yield a quantitative local Lipschitz bound
for the unique fitted vector and its coordinatewise logarithm.  Mathlib's
Rademacher theorem then gives almost-everywhere differentiability.
-/

open Set MeasureTheory Filter
open scoped BigOperators NNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Quantitative local Lipschitz bound for fitted values.  On a weight set with
coordinates at least `a`, and a feasible fitted set contained coordinatewise
in `[c,B]`, the constant is `n B²/(ac)` for the product sup norm. -/
theorem solution {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hCpos : C ⊆ positiveVectors n)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {s : Set (Fin n → ℝ)} {a c B : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hB : 0 < B)
    (hwa : ∀ w ∈ s, ∀ i, a ≤ w i)
    (hvc : ∀ w ∈ s, ∀ i, c ≤ vhat w i)
    (hvB : ∀ w ∈ s, ∀ i, vhat w i ≤ B)
    (hmax : ∀ w ∈ s, IsMaxOn C (weightedLogLikelihood w) (vhat w)) :
    LipschitzOnWith
      ⟨(n : ℝ) * B ^ 2 / (a * c), by positivity⟩ vhat s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro w hw u hu
  let dv : Fin n → ℝ := fun i ↦ vhat w i - vhat u i
  let dw : Fin n → ℝ := fun i ↦ w i - u i
  let S : ℝ := ∑ i, (dv i) ^ 2
  have hwfirst := fitted_maximizer_firstOrder_nonpos hC hCpos
    w (vhat w) (vhat u) (hmax w hw) (hmax u hu).1
  have hufirst := fitted_maximizer_firstOrder_nonpos hC hCpos
    u (vhat u) (vhat w) (hmax u hu) (hmax w hw).1
  have hwfirst' : 0 ≤ ∑ i, w i * (dv i / vhat w i) := by
    have heq : (∑ i, w i * ((vhat u i - vhat w i) / vhat w i)) =
        -(∑ i, w i * (dv i / vhat w i)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp [dv]
      ring
    rw [heq] at hwfirst
    linarith
  have hcompare : 0 ≤ ∑ i,
      (w i / vhat w i - u i / vhat u i) * dv i := by
    have heq : (∑ i, (w i / vhat w i - u i / vhat u i) * dv i) =
        (∑ i, w i * (dv i / vhat w i)) +
          -(∑ i, u i * ((vhat w i - vhat u i) / vhat u i)) := by
      calc
        (∑ i, (w i / vhat w i - u i / vhat u i) * dv i) =
            ∑ i, (w i * (dv i / vhat w i) -
              u i * ((vhat w i - vhat u i) / vhat u i)) := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp [dv]
          ring
        _ = (∑ i, w i * (dv i / vhat w i)) -
            ∑ i, u i * ((vhat w i - vhat u i) / vhat u i) :=
          by rw [Finset.sum_sub_distrib]
        _ = _ := by ring
    rw [heq]
    exact add_nonneg hwfirst' (neg_nonneg.mpr hufirst)
  have hidentity : (∑ i,
      (w i / vhat w i - u i / vhat u i) * dv i) =
      -(∑ i, w i * (dv i) ^ 2 / (vhat w i * vhat u i)) +
        ∑ i, dw i * dv i / vhat u i := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hvw0 : vhat w i ≠ 0 := (lt_of_lt_of_le hc (hvc w hw i)).ne'
    have hvu0 : vhat u i ≠ 0 := (lt_of_lt_of_le hc (hvc u hu i)).ne'
    dsimp [dv, dw]
    field_simp [hvw0, hvu0]
    ring
  have hcurv : (a / B ^ 2) * S ≤
      ∑ i, w i * (dv i) ^ 2 / (vhat w i * vhat u i) := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hvwpos : 0 < vhat w i := lt_of_lt_of_le hc (hvc w hw i)
    have hvupos : 0 < vhat u i := lt_of_lt_of_le hc (hvc u hu i)
    have hprod : vhat w i * vhat u i ≤ B ^ 2 := by
      rw [pow_two]
      exact mul_le_mul (hvB w hw i) (hvB u hu i)
        hvupos.le (le_trans hvupos.le (hvB u hu i))
    have hcoeff : a / B ^ 2 ≤ w i / (vhat w i * vhat u i) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hB) (mul_pos hvwpos hvupos)]
      calc
        a * (vhat w i * vhat u i) ≤ a * B ^ 2 :=
          mul_le_mul_of_nonneg_left hprod ha.le
        _ ≤ w i * B ^ 2 :=
          mul_le_mul_of_nonneg_right (hwa w hw i) (sq_nonneg B)
    have hsquare : 0 ≤ (dv i) ^ 2 := sq_nonneg _
    convert mul_le_mul_of_nonneg_right hcoeff hsquare using 1 <;> ring
  have hcross : ∑ i, dw i * dv i / vhat u i ≤
      (n : ℝ) / c * ‖w - u‖ * ‖vhat w - vhat u‖ := by
    calc
      ∑ i, dw i * dv i / vhat u i ≤
          ∑ _i : Fin n, (‖w - u‖ * ‖vhat w - vhat u‖ / c) := by
        apply Finset.sum_le_sum
        intro i _
        have hden : c ≤ vhat u i := hvc u hu i
        have hdenpos : 0 < vhat u i := lt_of_lt_of_le hc hden
        have hdw : |dw i| ≤ ‖w - u‖ := by
          simpa [dw, Real.norm_eq_abs] using norm_le_pi_norm (w - u) i
        have hdv : |dv i| ≤ ‖vhat w - vhat u‖ := by
          simpa [dv, Real.norm_eq_abs] using norm_le_pi_norm (vhat w - vhat u) i
        calc
          dw i * dv i / vhat u i ≤ |dw i * dv i / vhat u i| := le_abs_self _
          _ = |dw i| * |dv i| / vhat u i := by
            rw [abs_div, abs_mul, abs_of_pos hdenpos]
          _ ≤ (‖w - u‖ * ‖vhat w - vhat u‖) / vhat u i := by
            gcongr
          _ ≤ (‖w - u‖ * ‖vhat w - vhat u‖) / c := by
            exact div_le_div_of_nonneg_left
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hc hden
      _ = (n : ℝ) / c * ‖w - u‖ * ‖vhat w - vhat u‖ := by
        simp [div_eq_mul_inv]
        ring
  have hmain : (a / B ^ 2) * S ≤
      (n : ℝ) / c * ‖w - u‖ * ‖vhat w - vhat u‖ := by
    rw [hidentity] at hcompare
    linarith
  have hSnonneg : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ sq_nonneg (dv i)
  have hnormsqrt : ‖vhat w - vhat u‖ ≤ Real.sqrt S := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).2
    intro i
    simpa [dv, Real.norm_eq_abs] using abs_le_sqrt_sum_sq dv i
  have hnormsq : ‖vhat w - vhat u‖ ^ 2 ≤ S := by
    nlinarith [Real.sq_sqrt hSnonneg, norm_nonneg (vhat w - vhat u)]
  have hquad : (a / B ^ 2) * ‖vhat w - vhat u‖ ^ 2 ≤
      (n : ℝ) / c * ‖w - u‖ * ‖vhat w - vhat u‖ :=
    (mul_le_mul_of_nonneg_left hnormsq (div_nonneg ha.le (sq_nonneg B))).trans hmain
  change dist (vhat w) (vhat u) ≤
    ((n : ℝ) * B ^ 2 / (a * c)) * dist w u
  rw [dist_eq_norm, dist_eq_norm]
  by_cases hvzero : ‖vhat w - vhat u‖ = 0
  · rw [hvzero]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg B))
        (mul_nonneg ha.le hc.le)) (norm_nonneg _)
  · have hvpos : 0 < ‖vhat w - vhat u‖ := lt_of_le_of_ne
      (norm_nonneg _) (Ne.symm hvzero)
    have hscaled : a * c * ‖vhat w - vhat u‖ ≤
        (n : ℝ) * B ^ 2 * ‖w - u‖ := by
      have hquad' : a * c * ‖vhat w - vhat u‖ ^ 2 ≤
          (n : ℝ) * B ^ 2 * ‖w - u‖ * ‖vhat w - vhat u‖ := by
        calc
          a * c * ‖vhat w - vhat u‖ ^ 2 =
              (c * B ^ 2) * ((a / B ^ 2) * ‖vhat w - vhat u‖ ^ 2) := by
            field_simp [hB.ne']
          _ ≤ (c * B ^ 2) * ((n : ℝ) / c * ‖w - u‖ *
              ‖vhat w - vhat u‖) :=
            mul_le_mul_of_nonneg_left hquad (by positivity)
          _ = (n : ℝ) * B ^ 2 * ‖w - u‖ * ‖vhat w - vhat u‖ := by
            field_simp [hc.ne']
      apply (mul_le_mul_iff_right₀ hvpos).mp
      simpa only [mul_assoc, mul_left_comm, mul_comm, pow_two] using hquad'
    rw [show (n : ℝ) * B ^ 2 / (a * c) * ‖w - u‖ =
      ((n : ℝ) * B ^ 2 * ‖w - u‖) / (a * c) by ring]
    exact (le_div_iff₀ (mul_pos ha hc)).2 (by simpa [mul_comm] using hscaled)
