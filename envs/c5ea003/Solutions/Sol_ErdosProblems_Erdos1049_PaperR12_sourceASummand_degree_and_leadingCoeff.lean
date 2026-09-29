-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.sourceASummand_degree_and_leadingCoeff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:41:55.110866+00:00
-- url     : https://prove2.me/submissions/9ce04148-107a-4664-9219-9092a2270467

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_gaussian_monic_natDegree
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

















/-- Degree and monicity of the two actual source factors together. -/
theorem sourceGaussianProduct_monic_degree (n s : ℕ) (hs : s ≤ 13 * n) :
    (sourceGaussianProduct n s).Monic ∧
      (sourceGaussianProduct n s).natDegree =
        12 * n * (2 * n + s) + (13 * n - s) * s := by
  obtain ⟨h1, hd1⟩ := gaussian_monic_natDegree (14 * n + s) (12 * n) (by omega)
  obtain ⟨h2, hd2⟩ := gaussian_monic_natDegree (13 * n) (13 * n - s) (by omega)
  unfold sourceGaussianProduct
  constructor
  · exact h1.mul h2
  · rw [natDegree_mul' (by simp [h1.leadingCoeff, h2.leadingCoeff]), hd1, hd2]
    have he1 : 14 * n + s - 12 * n = 2 * n + s := by omega
    have he2 : 13 * n - (13 * n - s) = s := by omega
    rw [he1, he2]
end ErdosProblems.Erdos1049.PaperR12

open Polynomial
open PaperR11
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (n s : ℕ) (hs : s ≤ 13 * n) :
    (sourceASummand n s).natDegree = sourceASummandDegree n s ∧
      (sourceASummand n s).leadingCoeff = (-1 : ℤ) ^ s := by
  obtain ⟨hG, hdG⟩ := sourceGaussianProduct_monic_degree n s hs
  have hmono : ((X : ℤ[X]) ^ (sourceM n + sourceAExponent n s) *
      sourceGaussianProduct n s).Monic := (monic_X_pow _).mul hG
  have hs0 : (-1 : ℤ) ^ s ≠ 0 := pow_ne_zero _ (by norm_num)
  have hform : sourceASummand n s = C ((-1 : ℤ) ^ s) *
      (X ^ (sourceM n + sourceAExponent n s) * sourceGaussianProduct n s) := by
    unfold sourceASummand
    ring
  rw [hform]
  constructor
  · rw [natDegree_mul' (by simp [hmono.leadingCoeff, hs0]), natDegree_C, zero_add,
      natDegree_mul' (by simp [hG.leadingCoeff]), natDegree_X_pow, hdG]
    unfold sourceASummandDegree
    omega
  · exact hmono.leadingCoeff_C_mul _
