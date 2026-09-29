-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR13.actual_B_inclusion_iff_remainder
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:04:29.480838+00:00
-- url     : https://prove2.me/submissions/f31c1ff0-5b7b-4451-a5ac-97fcdd6835af

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



















































/-- Honest remainder-bearing division identity. -/
theorem actual_B_Omega_division (n : ℕ) :
    sourceOmegaRemainder n + sourceOmega n * sourceV n = sourceBWithoutMonomial n :=
  modByMonic_add_div _ _
end ErdosProblems.Erdos1049.PaperR13

open Polynomial PaperR11 PaperR12
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR13 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution (n : ℕ) :
    sourceClearedB n = sourceOmega n * X ^ sourceM n * sourceV n ↔
      sourceOmegaRemainder n = 0 := by
  have hX : (X : ℤ[X]) ^ sourceM n ≠ 0 := pow_ne_zero _ X_ne_zero
  rw [actual_B_monomial_factor]
  have hrearr : sourceOmega n * X ^ sourceM n * sourceV n =
      X ^ sourceM n * (sourceOmega n * sourceV n) := by ring
  rw [hrearr]
  have hdiv := actual_B_Omega_division n
  constructor
  · intro h
    have hc : sourceBWithoutMonomial n = sourceOmega n * sourceV n :=
      mul_left_cancel₀ hX h
    rw [hc] at hdiv
    exact add_right_cancel (show sourceOmegaRemainder n + sourceOmega n * sourceV n =
      0 + sourceOmega n * sourceV n by simpa using hdiv)
  · intro h
    have hc : sourceBWithoutMonomial n = sourceOmega n * sourceV n := by
      simpa only [h, zero_add] using hdiv.symm
    rw [hc]
