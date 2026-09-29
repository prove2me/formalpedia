-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.sourceASummandDegree_last
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:19:24.597166+00:00
-- url     : https://prove2.me/submissions/8044f514-ad13-4a41-9bb2-02efb8a276ff

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR11_twice_choose_two_int
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





























lemma twice_choose_two_nat (s : ℕ) : 2 * s.choose 2 + s = s * s := by
  have h := twice_choose_two_int s
  have hi : (2 : ℤ) * (s.choose 2 : ℤ) + (s : ℤ) = (s : ℤ) * (s : ℤ) := by
    nlinarith
  exact_mod_cast hi
end ErdosProblems.Erdos1049.PaperR12

open Polynomial
open PaperR11
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (n : ℕ) : sourceASummandDegree n (13 * n) = sourceK n := by
  have hc := twice_choose_two_nat (13 * n)
  have hd : 2 * sourceASummandDegree n (13 * n) = 1091 * n ^ 2 + 81 * n + 2 := by
    unfold sourceASummandDegree sourceAExponent sourceM
    simp only [Nat.sub_self, zero_mul, add_zero]
    nlinarith
  unfold sourceK
  omega
