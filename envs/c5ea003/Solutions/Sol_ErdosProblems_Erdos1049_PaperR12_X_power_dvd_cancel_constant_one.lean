-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.X_power_dvd_cancel_constant_one
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:42:48.634781+00:00
-- url     : https://prove2.me/submissions/d0558ece-1689-4273-9aec-dc5d00397617

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
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
theorem solution (c p : ℤ[X]) (m : ℕ)
    (hc : c.coeff 0 = 1) (h : (X : ℤ[X]) ^ m ∣ c * p) : X ^ m ∣ p := by
  classical
  have hz := Polynomial.X_pow_dvd_iff.mp h
  apply Polynomial.X_pow_dvd_iff.mpr
  have hcoeff : ∀ d : ℕ, d < m → p.coeff d = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro hd
        have hprod : (c * p).coeff d = p.coeff d := by
          rw [coeff_mul, Finset.sum_eq_single (0, d)]
          · simp [hc]
          · rintro ⟨i, j⟩ hij hne
            have hsum : i + j = d := Finset.mem_antidiagonal.mp hij
            have hjlt : j < d := by
              by_contra hh
              have hi0 : i = 0 := by omega
              have hjd : j = d := by omega
              exact hne (by simp [hi0, hjd])
            rw [ih j hjlt (by omega), mul_zero]
          · intro hnot
            exact (hnot (Finset.mem_antidiagonal.mpr (by omega))).elim
        rw [← hprod]
        exact hz d hd
  exact hcoeff
