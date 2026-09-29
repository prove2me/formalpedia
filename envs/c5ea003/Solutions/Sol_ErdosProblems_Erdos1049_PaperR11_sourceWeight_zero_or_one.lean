-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR11.sourceWeight_zero_or_one
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:51:27.463985+00:00
-- url     : https://prove2.me/submissions/3ae396e2-e68c-4933-8cfe-8b77d28c278f

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR11_omegaWeight_fract
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR7_omega_indicator
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































theorem omegaWeight_zero_or_one (x : ℝ) :
    PaperR7.omegaWeight x = 0 ∨ PaperR7.omegaWeight x = 1 := by
  have h := (PaperR7.omega_indicator (Int.fract x)
    (Int.fract_nonneg x) (Int.fract_lt_one x)).1
  simpa only [omegaWeight_fract] using h
end ErdosProblems.Erdos1049.PaperR11

open Polynomial
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (n l : ℕ) :
    sourceWeight n l = 0 ∨ sourceWeight n l = 1 := by
  exact omegaWeight_zero_or_one _
