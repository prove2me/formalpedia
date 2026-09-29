-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR13.quotient_remainder_successor_no_carry
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:14:27.312008+00:00
-- url     : https://prove2.me/submissions/5f7cfb98-3aa8-4d23-91b9-dd20e7aac0b6

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_RootUnityLocalCancellationR13
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



open ErdosProblems
open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.PaperR13
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR13 in
theorem solution {ell n : ℕ} (hell : 0 < ell)
    (h : n % ell + 1 < ell) :
    (n + 1) / ell = n / ell ∧ (n + 1) % ell = n % ell + 1 := by
  have hmod : (n + 1) % ell = n % ell + 1 := by
    rw [Nat.add_mod]
    have he : 1 % ell = 1 := Nat.mod_eq_of_lt (by omega)
    rw [he, Nat.mod_eq_of_lt h]
  exact ⟨Nat.succ_div_of_mod_ne_zero (by rw [hmod]; omega), hmod⟩
