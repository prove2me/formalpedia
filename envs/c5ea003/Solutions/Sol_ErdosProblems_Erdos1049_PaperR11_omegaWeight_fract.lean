-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR11.omegaWeight_fract
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:37:35.233841+00:00
-- url     : https://prove2.me/submissions/080c4456-2ab5-4d2d-aaae-2c1f3f6187de

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic

/-!
# Actual finite 2004 A coefficient and its normalisation


The reindexing k = 14*n+1+s makes every exponent nonnegative. In particular
A is an actual integral polynomial, not a postulated source package.
This module proves the A-channel inclusion for every n, including n=0.
It does not assert the missing B-channel cancellation or the analytic source
identity. Those obligations are recorded separately, not hidden in a premise.
-/

namespace ErdosProblems.Erdos1049.PaperR11
open Polynomial
open scoped BigOperators



























/-- Integer shifts in the floor argument cancel in each balanced floor sum. -/
lemma floor_mul_fract (x : ℝ) (a : ℤ) :
    ⌊(a : ℝ) * Int.fract x⌋ = ⌊(a : ℝ) * x⌋ - a * ⌊x⌋ := by
  change ⌊(a : ℝ) * (x - (⌊x⌋ : ℝ))⌋ = _
  rw [mul_sub, ← Int.cast_mul, Int.floor_sub_intCast]
end ErdosProblems.Erdos1049.PaperR11

open Polynomial
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (x : ℝ) :
    PaperR7.omegaWeight (Int.fract x) = PaperR7.omegaWeight x := by
  have h12 : ⌊(12 : ℝ) * Int.fract x⌋ = ⌊(12 : ℝ) * x⌋ - 12 * ⌊x⌋ := by
    simpa using floor_mul_fract x 12
  have h13 : ⌊(13 : ℝ) * Int.fract x⌋ = ⌊(13 : ℝ) * x⌋ - 13 * ⌊x⌋ := by
    simpa using floor_mul_fract x 13
  have h14 : ⌊(14 : ℝ) * Int.fract x⌋ = ⌊(14 : ℝ) * x⌋ - 14 * ⌊x⌋ := by
    simpa using floor_mul_fract x 14
  have h15 : ⌊(15 : ℝ) * Int.fract x⌋ = ⌊(15 : ℝ) * x⌋ - 15 * ⌊x⌋ := by
    simpa using floor_mul_fract x 15
  unfold PaperR7.omegaWeight
  rw [h12, h13, h14, h15]
  congr 2 <;> ring
