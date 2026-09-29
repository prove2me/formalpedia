-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR13.root_block_digits_carry
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T01:22:10.096305+00:00
-- url     : https://prove2.me/submissions/dc3aa3e3-9e51-449d-be71-c8c6e9df314b

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_RootUnityLocalCancellationR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBTopDegreeR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootCarriesR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootBlocksR13
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

namespace PaperR12
end PaperR12

namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators
end ErdosProblems.Erdos1049.PaperR13

open ErdosProblems
open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR13 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution (a t h ell : ℕ) (hell : 0 < ell)
    (hlo : ell ≤ a % ell + h) (hhi : a % ell + h < 2 * ell) :
    (a + t * ell + h) / ell = a / ell + t + 1 ∧
      (a + t * ell + h) % ell = a % ell + h - ell := by
  have ha := Nat.mod_add_div a ell
  have hre : a % ell + h - ell + ell = a % ell + h := by omega
  have hid : a + t * ell + h =
      (a / ell + t + 1) * ell + (a % ell + h - ell) := by
    nlinarith [ha, hre]
  have hd : (a + t * ell + h) / ell = a / ell + t + 1 := by
    apply (Nat.div_eq_iff hell).mpr
    constructor <;> omega
  have hr := Nat.mod_add_div (a + t * ell + h) ell
  rw [hd] at hr
  have he : (a + t * ell + h) % ell + ell = a % ell + h := by nlinarith
  exact ⟨hd, by omega⟩
