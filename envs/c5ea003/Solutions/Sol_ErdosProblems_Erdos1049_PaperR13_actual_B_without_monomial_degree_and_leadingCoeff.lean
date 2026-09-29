-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR13.actual_B_without_monomial_degree_and_leadingCoeff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:43:59.15165+00:00
-- url     : https://prove2.me/submissions/5b64d34b-6e36-4f33-97bf-298706523af8

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBTopDegreeR13
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_actual_B_monomial_factor
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_actual_B_without_monomial_ne_zero
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_actual_cleared_B_degree_and_leadingCoeff
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

/-!
# Exact top degree of the literal cleared B numerator



The unique leading term is the unshifted pair (s,l)=(13*n,1).
This is a finite polynomial proof: neither A*F-B=H nor Omega divisibility
is an assumption. The canonical monic quotient V is defined even before
its remainder is known to vanish; its degree is not misrepresented as
proof that this remainder vanishes.
-/

namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12
open scoped BigOperators
end ErdosProblems.Erdos1049.PaperR13

open Polynomial PaperR11 PaperR12
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR13 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (sourceBWithoutMonomial n).natDegree = sourceClearedBTop n - sourceM n ∧
    (sourceBWithoutMonomial n).leadingCoeff = (-1 : ℤ) ^ (13 * n) := by
  obtain ⟨hd, hc⟩ := actual_cleared_B_degree_and_leadingCoeff n hn
  have hf := actual_B_monomial_factor n
  have hb := congrArg Polynomial.natDegree hf
  rw [natDegree_mul' (by
      simpa only [leadingCoeff_X_pow, one_mul] using
        leadingCoeff_ne_zero.mpr (actual_B_without_monomial_ne_zero n hn)),
    natDegree_X_pow, hd] at hb
  constructor
  · omega
  · have hh := congrArg Polynomial.leadingCoeff hf
    rw [leadingCoeff_mul, leadingCoeff_X_pow, one_mul, hc] at hh
    exact hh.symm
