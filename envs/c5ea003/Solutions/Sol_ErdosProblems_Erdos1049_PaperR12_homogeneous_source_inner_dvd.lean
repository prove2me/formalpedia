-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.homogeneous_source_inner_dvd
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:59:53.441179+00:00
-- url     : https://prove2.me/submissions/e0e9102e-b912-4f2e-90a0-14cfcbaad2e3

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
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_X_power_dvd_cancel_constant_one
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_homogeneousPochhammer_factor
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_homogeneousPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_X_constantCoeff
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_homogeneous_source_transform_polynomial
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
theorem solution (n u : ℕ) (hu : u < 13 * n) :
    (X : ℤ[X]) ^ sourceHomogeneousOrder n u ∣
      homogeneousSourceInner X (X ^ u) (12 * n + 1) (2 * n) (13 * n + 1) := by
  apply X_power_dvd_cancel_constant_one
    (qPochhammer (X : ℤ[X]) X (12 * n)) _ (sourceHomogeneousOrder n u)
  · exact qPochhammer_X_constantCoeff (12 * n)
  · have ht := homogeneous_source_transform_polynomial u
      (a := 12 * n + 1) (d := 2 * n) (v := 13 * n + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at ht
    rw [ht]
    apply Finset.dvd_sum
    intro h hh
    by_cases hhu : h ≤ u
    · rw [homogeneousPochhammer_zero u h (13 * n) hu hhu, mul_zero]
      exact dvd_zero _
    · have huh : u < h := by omega
      rw [homogeneousPochhammer_factor u h (13 * n) huh]
      have hc := Nat.choose_le_choose 2 (show u + 1 ≤ h by omega)
      have hm := Nat.mul_le_mul_right (2 * n + 1) (show u + 1 ≤ h by omega)
      have he : sourceHomogeneousOrder n u ≤
          (h * (2 * n + 1) + h.choose 2) + u * (13 * n) := by
        unfold sourceHomogeneousOrder
        nlinarith
      have hid : (-1 : ℤ[X]) ^ h * X ^ (h * (2 * n + 1) + h.choose 2) *
          gaussBinom X (12 * n) h *
            (X ^ (u * (13 * n)) * ∏ i ∈ Finset.range (13 * n),
              (1 - X ^ (h + i - u))) =
          X ^ ((h * (2 * n + 1) + h.choose 2) + u * (13 * n)) *
            ((-1 : ℤ[X]) ^ h * gaussBinom X (12 * n) h *
              ∏ i ∈ Finset.range (13 * n), (1 - X ^ (h + i - u))) := by
        rw [pow_add]
        ring
      rw [hid]
      exact dvd_mul_of_dvd_left (X_power_dvd_of_le _ _ he) _
