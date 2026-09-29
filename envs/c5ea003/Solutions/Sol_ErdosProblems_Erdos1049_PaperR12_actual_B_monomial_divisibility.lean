-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.actual_B_monomial_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:10:05.558554+00:00
-- url     : https://prove2.me/submissions/af94e7a1-fcd8-465e-b294-2dc2f778a561

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR11_sourceASummand_factor
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_actual_shifted_A_sum_monomial_dvd
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceClearedB_reordered
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
theorem solution (n : ℕ) :
    (X : ℤ[X]) ^ sourceM n ∣ sourceClearedB n := by
  rw [sourceClearedB_reordered]
  apply dvd_add
  · apply Finset.dvd_sum
    intro s hs
    apply Finset.dvd_sum
    intro l hl
    refine ⟨sourceNormalisedASummand n s * sourceDQuotient n l, ?_⟩
    rw [sourceASummand_factor, mul_assoc]
  · apply Finset.dvd_sum
    intro j hj
    exact dvd_mul_of_dvd_left
      (actual_shifted_A_sum_monomial_dvd n j (Finset.mem_Icc.mp hj).2) _
