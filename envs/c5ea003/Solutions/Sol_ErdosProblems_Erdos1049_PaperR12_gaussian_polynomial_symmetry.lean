-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.gaussian_polynomial_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:03:56.821517+00:00
-- url     : https://prove2.me/submissions/56ccc19e-3597-4192-a769-6900b2cae44f

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_mul_qPochhammer_qPochhammer
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_X_ne_zero
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
# Exact Gaussian and actual A degrees


The unique highest summand is proved at every index; finite reconstructions
are not used to infer a polynomial identity. The integer coefficient mass of
each Gaussian is also evaluated exactly, rather than bounding one coefficient
and silently treating that as an l1 bound.
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
theorem solution (n k : ℕ) (hk : k ≤ n) :
    gaussBinom (X : ℤ[X]) n k = gaussBinom X n (n - k) := by
  have hnk : n - k ≤ n := Nat.sub_le n k
  have hsub : n - (n - k) = k := Nat.sub_sub_self hk
  have h1 := gaussBinom_mul_qPochhammer_qPochhammer (X : ℤ[X]) n k hk
  have h2 := gaussBinom_mul_qPochhammer_qPochhammer (X : ℤ[X]) n (n - k) hnk
  rw [hsub] at h2
  apply mul_right_cancel₀ (mul_ne_zero (qPochhammer_X_ne_zero k)
    (qPochhammer_X_ne_zero (n - k)))
  calc
    _ = qPochhammer X X n := by simpa only [mul_assoc] using h1
    _ = _ := by simpa only [mul_assoc, mul_comm, mul_left_comm] using h2.symm
