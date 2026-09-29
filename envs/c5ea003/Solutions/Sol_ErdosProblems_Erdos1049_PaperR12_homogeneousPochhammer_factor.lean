-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.homogeneousPochhammer_factor
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:46:01.325752+00:00
-- url     : https://prove2.me/submissions/8196ffea-eca5-4a8d-b753-607a5b5a3ded

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
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
# Homogeneous finite transform and monomial cancellation tools

Homogenisation removes the need to assert
that a Laurent expression is an integral polynomial. The identity is first
proved in a field, then pulled back through the injective fraction-field map.
The final displayed identity is entirely in Z[X].
-/

namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open scoped BigOperators
end ErdosProblems.Erdos1049.PaperR12

open Polynomial
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution (u h N : ℕ) (hh : u < h) :
    homogeneousPochhammer (X : ℤ[X]) (X ^ u) h N =
      X ^ (u * N) * ∏ i ∈ Finset.range N, (1 - X ^ (h + i - u)) := by
  have hf (i : ℕ) : (X : ℤ[X]) ^ u - X ^ (h + i) =
      X ^ u * (1 - X ^ (h + i - u)) := by
    have he : u + (h + i - u) = h + i := by omega
    rw [mul_sub, mul_one, ← pow_add, he]
  unfold homogeneousPochhammer
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_range, ← pow_mul]
