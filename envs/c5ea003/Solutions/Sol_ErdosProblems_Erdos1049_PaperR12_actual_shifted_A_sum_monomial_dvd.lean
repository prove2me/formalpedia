-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.actual_shifted_A_sum_monomial_dvd
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:07:43.485605+00:00
-- url     : https://prove2.me/submissions/5e695b3a-7bfd-4841-8030-1868d0bf5862

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_X_power_dvd_of_le
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_X_power_dvd_signed_summand
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_homogeneous_source_inner_dvd
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceHomogeneousBase_order
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceShiftedASum_homogeneous
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





lemma sourceShiftedASummand_early_dvd (n s j : ℕ) (hj : j ≤ n) :
    (X : ℤ[X]) ^ sourceM n ∣ sourceShiftedASummand n s j := by
  have hmul := Nat.mul_le_mul_right (2 * n + s) hj
  have hexp : j * (2 * n + s) ≤ sourceAExponent n s := by
    unfold sourceAExponent
    nlinarith [Nat.zero_le (s.choose 2)]
  unfold sourceShiftedASummand
  apply X_power_dvd_signed_summand
  omega
end ErdosProblems.Erdos1049.PaperR12

open Polynomial
open PaperR11
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (n j : ℕ) (hj : j ≤ 14 * n) :
    (X : ℤ[X]) ^ sourceM n ∣ sourceShiftedASum n j := by
  by_cases hearly : j ≤ n
  · unfold sourceShiftedASum
    exact Finset.dvd_sum (fun s _ => sourceShiftedASummand_early_dvd n s j hearly)
  · let u := j - n - 1
    have hu : u < 13 * n := by dsimp [u]; omega
    have hju : j = n + u + 1 := by dsimp [u]; omega
    obtain ⟨v, hv⟩ := homogeneous_source_inner_dvd n u hu
    rw [sourceShiftedASum_homogeneous n j u hj hu hju, hv, ← mul_assoc, ← pow_add]
    have he : sourceM n ≤ sourceHomogeneousBase n j u + sourceHomogeneousOrder n u := by
      rw [sourceHomogeneousBase_order n j u hj hu hju]
      omega
    exact dvd_mul_of_dvd_left (X_power_dvd_of_le _ _ he) v
