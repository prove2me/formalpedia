-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.sourceComplement_monic_degree
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:24:18.391761+00:00
-- url     : https://prove2.me/submissions/346c5d16-59a2-4fa6-8310-d510f25e17e4

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
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
    (sourceComplement n).Monic ∧ (sourceComplement n).natDegree =
      ∑ l ∈ Finset.Icc 1 (15 * n), if sourceWeight n l = 0 then l.totient else 0 := by
  classical
  have hall (s : Finset ℕ) :
      (∏ l ∈ s, if sourceWeight n l = 0 then cyclotomic l ℤ else 1).Monic ∧
      (∏ l ∈ s, if sourceWeight n l = 0 then cyclotomic l ℤ else 1).natDegree =
        ∑ l ∈ s, if sourceWeight n l = 0 then l.totient else 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert l s hls ih =>
        rw [Finset.prod_insert hls, Finset.sum_insert hls]
        have hm : (if sourceWeight n l = 0 then cyclotomic l ℤ else (1 : ℤ[X])).Monic := by
          split_ifs
          · exact cyclotomic.monic l ℤ
          · exact monic_one
        constructor
        · exact hm.mul ih.1
        · rw [natDegree_mul' (by simp [hm.leadingCoeff, ih.1.leadingCoeff]), ih.2]
          split_ifs <;> simp [natDegree_cyclotomic]
  exact hall _
