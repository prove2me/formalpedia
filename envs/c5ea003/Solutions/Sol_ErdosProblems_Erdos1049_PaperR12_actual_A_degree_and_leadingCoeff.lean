-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.actual_A_degree_and_leadingCoeff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:46:21.396871+00:00
-- url     : https://prove2.me/submissions/8f588aaf-7f37-40a6-a655-17cce64eb05c

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_polynomial_sum_natDegree_le
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceASummandDegree_last
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceASummandDegree_strict
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceASummand_degree_and_leadingCoeff
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
theorem solution (n : ℕ) :
    (sourceA n).natDegree = sourceK n ∧
      (sourceA n).leadingCoeff = (-1 : ℤ) ^ (13 * n) := by
  classical
  have hlast := sourceASummand_degree_and_leadingCoeff n (13 * n) le_rfl
  have hbound : (sourceA n).natDegree ≤ sourceASummandDegree n (13 * n) := by
    unfold sourceA
    apply polynomial_sum_natDegree_le
    intro s hs
    have hs' : s ≤ 13 * n := by have hh := Finset.mem_range.mp hs; omega
    rw [(sourceASummand_degree_and_leadingCoeff n s hs').1]
    rcases lt_or_eq_of_le hs' with hlt | rfl
    · exact (sourceASummandDegree_strict n hlt le_rfl).le
    · exact le_rfl
  have hcoeff : (sourceA n).coeff (sourceASummandDegree n (13 * n)) =
      (-1 : ℤ) ^ (13 * n) := by
    unfold sourceA
    rw [finset_sum_coeff]
    rw [Finset.sum_eq_single (13 * n)]
    · rw [← hlast.1, coeff_natDegree, hlast.2]
    · intro s hs hne
      have hs' : s < 13 * n := by have hh := Finset.mem_range.mp hs; omega
      apply coeff_eq_zero_of_natDegree_lt
      rw [(sourceASummand_degree_and_leadingCoeff n s hs'.le).1]
      exact sourceASummandDegree_strict n hs' le_rfl
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim
  have hdegree : (sourceA n).natDegree = sourceASummandDegree n (13 * n) :=
    natDegree_eq_of_le_of_coeff_ne_zero hbound
      (by rw [hcoeff]; exact pow_ne_zero _ (by norm_num : (-1 : ℤ) ≠ 0))
  constructor
  · exact hdegree.trans (sourceASummandDegree_last n)
  · change (sourceA n).coeff (sourceA n).natDegree = _
    rw [hdegree, hcoeff]
