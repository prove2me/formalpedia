-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR13.qPochhammer_nonzero_below_order
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:07:43.415302+00:00
-- url     : https://prove2.me/submissions/1ecbe975-2d02-4a6a-9ed3-bb09dc7804bd

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_RootUnityLocalCancellationR13
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_succ
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

namespace ErdosProblems.Erdos1049.PaperR13
open Finset
open scoped BigOperators
variable {K : Type*} [Field K]
end ErdosProblems.Erdos1049.PaperR13

open ErdosProblems
open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.PaperR13
open Finset
open scoped BigOperators
variable {K : Type*} [Field K]
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR13 in
theorem solution (q : K) {ell : ℕ}
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1) :
    ∀ a : ℕ, a < ell → qPochhammer q q a ≠ 0 := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
      intro ha
      rw [qPochhammer_succ]
      apply mul_ne_zero (ih (by omega))
      rw [← pow_succ']
      exact sub_ne_zero.mpr (hprimitive (a + 1) (by omega) ha).symm
