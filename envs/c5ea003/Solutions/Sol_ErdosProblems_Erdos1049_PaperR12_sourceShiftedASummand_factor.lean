-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand_factor
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:36:25.723987+00:00
-- url     : https://prove2.me/submissions/01f6990d-139c-4947-8fc5-f53361c92e3a

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
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
# Literal B coefficient and its first polynomial clearing


This constructs the finite source expression itself, including its negative
powers, and proves D*B is an integral polynomial. It does NOT claim the
additional X^M or Omega cancellation. No polynomial-inclusion hypothesis is
used in the construction or the clearing theorem.
-/

namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open scoped BigOperators
open PaperR11







/-- This arithmetic check prevents natural subtraction from hiding a negative
raw exponent in the second channel of B. -/
lemma source_shift_exponent_le (n s j : ℕ) (hs : s ≤ 13 * n)
    (hj : j ≤ 14 * n) :
    j * (2 * n + s) ≤ sourceM n + sourceAExponent n s := by
  have hprod : j * (2 * n + s) ≤ (14 * n) * (15 * n) :=
    Nat.mul_le_mul hj (by omega)
  unfold sourceM sourceAExponent
  nlinarith [Nat.zero_le (s.choose 2), Nat.zero_le ((n + 1) * s)]
end ErdosProblems.Erdos1049.PaperR12

open Polynomial
open scoped BigOperators
open PaperR11
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (n s j : ℕ) (hs : s ≤ 13 * n)
    (hj : j ≤ 14 * n) :
    X ^ (j * (2 * n + s)) * sourceShiftedASummand n s j =
      sourceASummand n s := by
  have hb := source_shift_exponent_le n s j hs hj
  have he : j * (2 * n + s) +
      (sourceM n + sourceAExponent n s - j * (2 * n + s)) =
      sourceM n + sourceAExponent n s := by omega
  unfold sourceShiftedASummand sourceASummand
  calc
    _ = C ((-1 : ℤ) ^ s) *
        (X ^ (j * (2 * n + s)) *
          X ^ (sourceM n + sourceAExponent n s - j * (2 * n + s))) *
          sourceGaussianProduct n s := by ring
    _ = _ := by rw [← pow_add, he]
