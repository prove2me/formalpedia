-- Prove2me | solution 1 for Erdos146.withoutReplacementBinaryPairExpectation_error
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:05:18.758106+00:00
-- url     : https://prove2.me/submissions/f09ca26a-daac-42cf-967b-06d4c09cbfa0

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem withoutReplacementBinaryPairExpectation_sub
    (parentCount oneCount : ℕ) (hparents : 2 ≤ parentCount)
    (f : Bool → Bool → ℝ) :
    withoutReplacementBinaryPairExpectation parentCount oneCount f -
        (∑ left : Bool, ∑ right : Bool,
          independentBinaryPairMass
            ((oneCount : ℝ) / (parentCount : ℝ)) left right *
              f left right) =
      (((oneCount : ℝ) / (parentCount : ℝ)) *
        (1 - (oneCount : ℝ) / (parentCount : ℝ)) /
          ((parentCount : ℝ) - 1)) *
        (f false true + f true false - f false false - f true true) := by
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  simp [withoutReplacementBinaryPairExpectation, Fintype.univ_bool,
    withoutReplacementBinaryPairMass, empiricalBinaryOutcomeCount,
    independentBinaryPairMass, binaryCoinMass]
  field_simp [hparent_real.ne', hparent_minus.ne']
  ring

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, 0 ≤ f left right ∧ f left right ≤ 1) :
    |withoutReplacementBinaryPairExpectation parentCount oneCount f -
        (∑ left : Bool, ∑ right : Bool,
          independentBinaryPairMass
            ((oneCount : ℝ) / (parentCount : ℝ)) left right *
              f left right)| ≤ 1 / (parentCount : ℝ) := by
  let q : ℝ := (oneCount : ℝ) / (parentCount : ℝ)
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  have hqzero : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqone : q ≤ 1 := by
    dsimp [q]
    apply (div_le_one hparent_real).mpr
    exact_mod_cast hones
  have hvariance : q * (1 - q) ≤ (1 : ℝ) / 4 := by
    nlinarith [sq_nonneg (q - 1 / 2)]
  have hscaledvariance :=
    mul_le_mul_of_nonneg_right hvariance hparent_real.le
  have hdelta_nonneg : 0 ≤ q * (1 - q) / ((parentCount : ℝ) - 1) := by
    exact div_nonneg
      (mul_nonneg hqzero (sub_nonneg.mpr hqone))
      hparent_minus.le
  have hdelta_bound :
      2 * (q * (1 - q) / ((parentCount : ℝ) - 1)) ≤
        1 / (parentCount : ℝ) := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    rw [show 2 * (q * (1 - q) / ((parentCount : ℝ) - 1)) =
      (2 * (q * (1 - q))) / ((parentCount : ℝ) - 1) by ring]
    apply (div_le_div_iff₀ hparent_minus hparent_real).mpr
    nlinarith
  have hbracket :
      |f false true + f true false - f false false - f true true| ≤
        (2 : ℝ) := by
    rw [abs_le]
    have h₀₀ := hf false false
    have h₀₁ := hf false true
    have h₁₀ := hf true false
    have h₁₁ := hf true true
    constructor <;> linarith
  rw [withoutReplacementBinaryPairExpectation_sub
    parentCount oneCount hparents f, abs_mul]
  change
    |q * (1 - q) / ((parentCount : ℝ) - 1)| *
        |f false true + f true false - f false false - f true true| ≤
      1 / (parentCount : ℝ)
  rw [abs_of_nonneg hdelta_nonneg]
  calc
    (q * (1 - q) / ((parentCount : ℝ) - 1)) *
        |f false true + f true false - f false false - f true true| ≤
      (q * (1 - q) / ((parentCount : ℝ) - 1)) * 2 :=
        mul_le_mul_of_nonneg_left hbracket hdelta_nonneg
    _ ≤ 1 / (parentCount : ℝ) := by
      nlinarith
