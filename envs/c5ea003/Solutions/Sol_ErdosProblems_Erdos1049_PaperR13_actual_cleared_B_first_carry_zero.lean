-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR13.actual_cleared_B_first_carry_zero
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:30:27.713238+00:00
-- url     : https://prove2.me/submissions/08ab85c5-0b2a-4e30-8a6d-b1f8ca38a28f

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
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceShiftedASummand_map
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_actual_source_gaussian_product_first_carry_zero
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
open Polynomial PaperR11 PaperR12
open scoped BigOperators
variable {K : Type*} [Field K]
/-- Every actual A residue is zero in the first carry case. -/
theorem actual_ASummand_first_carry_zero (q : K) (hq : q ≠ 0)
    (n ell s : ℕ) (hell : 0 < ell) (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1)
    (hcarry : sourceCarryOne n ell = 1) (hs : s ≤ 13 * n) :
    (sourceASummand n s).eval₂ (Int.castRingHom K) q = 0 := by
  simp only [sourceASummand, eval₂_mul]
  rw [actual_source_gaussian_product_first_carry_zero q hq n ell s hell hroot hprimitive hcarry hs]
  ring
end ErdosProblems.Erdos1049.PaperR13

open ErdosProblems
open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12
open scoped BigOperators
variable {K : Type*} [Field K]
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR13 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution (q : K) (hq : q ≠ 0)
    (n ell : ℕ) (hell : 0 < ell) (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1)
    (hcarry : sourceCarryOne n ell = 1) :
    (sourceClearedB n).eval₂ (Int.castRingHom K) q = 0 := by
  classical
  let f : ℤ[X] →+* K := Polynomial.eval₂RingHom (Int.castRingHom K) q
  change f (sourceClearedB n) = 0
  unfold sourceClearedB
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro s hs
  have hs' : s ≤ 13 * n := by have := Finset.mem_range.mp hs; omega
  have hA : f (sourceASummand n s) = 0 :=
    actual_ASummand_first_carry_zero q hq n ell s hell hroot hprimitive hcarry hs'
  rw [map_add, map_sum, map_sum]
  have hleft : (∑ l ∈ Finset.Icc 1 (2 * n + s),
      f (sourceASummand n s * sourceDQuotient n l)) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [map_mul, hA, zero_mul]
  have hright : (∑ j ∈ Finset.Icc 1 (14 * n),
      f (sourceShiftedASummand n s j * sourceDQuotient n j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [map_mul, sourceShiftedASummand_map f n s j hs' (Finset.mem_Icc.mp hj).2
      (by simpa [f] using hq), hA, zero_mul, zero_mul]
  rw [hleft, hright, zero_add]
