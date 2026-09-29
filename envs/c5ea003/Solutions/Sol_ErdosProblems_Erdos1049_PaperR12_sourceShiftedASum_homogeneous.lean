-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.sourceShiftedASum_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:06:15.792375+00:00
-- url     : https://prove2.me/submissions/2b1c3400-1e67-40e3-8147-1d59655c80e3

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_gaussian_polynomial_symmetry
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_source_shift_homogeneous_exponent
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
# The actual B monomial cancellation



The late j-channel is treated by a homogeneous finite identity in Z[X].
No endpoint divisibility, Laurent membership, source package, or initial-order
assertion is assumed. This removes X^M from the actual integral numerator D*B.
The additional cyclotomic Omega cancellation is a different theorem and is
not asserted in this file.
-/

namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open PaperR11
open scoped BigOperators
end ErdosProblems.Erdos1049.PaperR12

open Polynomial
open PaperR11
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (n j u : ℕ) (hj : j ≤ 14 * n)
    (hu : u < 13 * n) (hju : j = n + u + 1) :
    sourceShiftedASum n j = (X : ℤ[X]) ^ sourceHomogeneousBase n j u *
      homogeneousSourceInner X (X ^ u) (12 * n + 1) (2 * n) (13 * n + 1) := by
  unfold sourceShiftedASum homogeneousSourceInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s ≤ 13 * n := by have hh := Finset.mem_range.mp hs; omega
  have he := source_shift_homogeneous_exponent n s j u hs' hj hu hju
  have hg : gaussBinom (X : ℤ[X]) (13 * n) (13 * n - s) =
      gaussBinom X (13 * n) s := (gaussian_polynomial_symmetry (13 * n) s hs').symm
  have hi1 : 13 * n + 1 - 1 = 13 * n := by omega
  have hi2 : 12 * n + 1 - 1 = 12 * n := by omega
  have hi3 : 12 * n + 1 + 2 * n + s - 1 = 14 * n + s := by omega
  have hsign : (C ((-1 : ℤ) ^ s) : ℤ[X]) = (-1 : ℤ[X]) ^ s := by simp
  unfold sourceShiftedASummand sourceGaussianProduct
  rw [he, hg, hi1, hi2, hi3, hsign]
  simp only [pow_add, pow_mul]
  ring
