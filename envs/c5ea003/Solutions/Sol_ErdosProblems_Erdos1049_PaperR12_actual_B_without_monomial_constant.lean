-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.actual_B_without_monomial_constant
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:35:17.151336+00:00
-- url     : https://prove2.me/submissions/95e00d4d-529f-4053-ad4f-5356908ae33d

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_actual_B_monomial_factor
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_actual_B_initial_coefficient
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

namespace PaperR11
end PaperR11

/-!
# Exact initial coefficient of the actual B numerator


The numerator is divisible by X^M but not X^(M+1): at every n>=1 its
coefficient at M is exactly 1. This is proved by isolating the actual j=n,
s=0 channel. No finite reconstruction or initial-order hypothesis is used.
-/

namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial PaperR11
open scoped BigOperators
end ErdosProblems.Erdos1049.PaperR12

open Polynomial PaperR11
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (sourceBWithoutMonomial n).coeff 0 = 1 := by
  have h := actual_B_initial_coefficient n hn
  rw [actual_B_monomial_factor, coeff_X_pow_mul'] at h
  simpa only [le_refl, if_true, Nat.sub_self] using h
