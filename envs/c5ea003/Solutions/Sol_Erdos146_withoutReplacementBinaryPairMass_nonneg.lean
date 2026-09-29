-- Prove2me | solution 1 for Erdos146.withoutReplacementBinaryPairMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:04:37.251412+00:00
-- url     : https://prove2.me/submissions/806accc1-fcf1-44e6-b71d-b2778fc36132

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (left right : Bool) :
    0 ≤ withoutReplacementBinaryPairMass parentCount oneCount left right := by
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  have hdenominator :
      0 ≤ (parentCount : ℝ) * ((parentCount : ℝ) - 1) :=
    (mul_pos hparent_real hparent_minus).le
  have hone_nonneg : (0 : ℝ) ≤ (oneCount : ℝ) := by positivity
  have hcount : (oneCount : ℝ) ≤ (parentCount : ℝ) := by
    exact_mod_cast hones
  have hzero_nonneg : 0 ≤ (parentCount : ℝ) - (oneCount : ℝ) := by
    linarith
  have hone_diagonal :
      0 ≤ (oneCount : ℝ) * ((oneCount : ℝ) - 1) := by
    by_cases hzero : oneCount = 0
    · simp [hzero]
    · have hone : 1 ≤ oneCount := Nat.one_le_iff_ne_zero.mpr hzero
      have hone_real : (1 : ℝ) ≤ (oneCount : ℝ) := by
        exact_mod_cast hone
      positivity
  have hzero_diagonal :
      0 ≤ ((parentCount : ℝ) - (oneCount : ℝ)) *
        ((parentCount : ℝ) - (oneCount : ℝ) - 1) := by
    by_cases hfull : oneCount = parentCount
    · simp [hfull]
    · have hstrict : oneCount < parentCount :=
        lt_of_le_of_ne hones hfull
      have hsucc : oneCount + 1 ≤ parentCount := by omega
      have hsucc_real :
          (oneCount : ℝ) + 1 ≤ (parentCount : ℝ) := by
        exact_mod_cast hsucc
      have hfactor :
          0 ≤ (parentCount : ℝ) - (oneCount : ℝ) - 1 := by
        linarith
      exact mul_nonneg hzero_nonneg hfactor
  cases left <;> cases right
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg hzero_diagonal hdenominator
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg (mul_nonneg hzero_nonneg hone_nonneg) hdenominator
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg (mul_nonneg hone_nonneg hzero_nonneg) hdenominator
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg hone_diagonal hdenominator
