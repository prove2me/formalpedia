-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.actual_U_degree
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:58:30.862642+00:00
-- url     : https://prove2.me/submissions/f5e6df63-18b4-42cf-9f3b-f8362934ff08

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR11_sourceA_factor
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_actual_A_degree_and_leadingCoeff
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceComplement_monic_degree
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





































theorem actual_A_ne_zero (n : ℕ) : sourceA n ≠ 0 := by
  apply leadingCoeff_ne_zero.mp
  rw [(actual_A_degree_and_leadingCoeff n).2]
  exact pow_ne_zero _ (by norm_num)

theorem actual_A_without_monomial_ne_zero (n : ℕ) : sourceAWithoutMonomial n ≠ 0 := by
  intro h
  have hz : sourceA n = 0 := by rw [sourceA_factor, h, mul_zero]
  exact actual_A_ne_zero n hz

theorem actual_A_without_monomial_degree (n : ℕ) :
    (sourceAWithoutMonomial n).natDegree = sourceK n - sourceM n := by
  have hd := (actual_A_degree_and_leadingCoeff n).1
  rw [sourceA_factor, natDegree_mul' (by
      simpa only [leadingCoeff_X_pow, one_mul] using
        (leadingCoeff_ne_zero.mpr (actual_A_without_monomial_ne_zero n))),
    natDegree_X_pow] at hd
  omega
end ErdosProblems.Erdos1049.PaperR12

open Polynomial
open PaperR11
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (n : ℕ) :
    (sourceU n).natDegree = sourceK n - sourceM n +
      ∑ l ∈ Finset.Icc 1 (15 * n), if sourceWeight n l = 0 then l.totient else 0 := by
  obtain ⟨hC, hdC⟩ := sourceComplement_monic_degree n
  unfold sourceU
  rw [natDegree_mul' (by
    simpa only [hC.leadingCoeff, one_mul] using
      (leadingCoeff_ne_zero.mpr (actual_A_without_monomial_ne_zero n))),
    hdC, actual_A_without_monomial_degree]
  omega
