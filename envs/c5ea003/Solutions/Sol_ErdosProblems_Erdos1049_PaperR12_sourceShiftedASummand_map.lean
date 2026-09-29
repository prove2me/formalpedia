-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand_map
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:59:49.061658+00:00
-- url     : https://prove2.me/submissions/f9aca668-f468-4614-8bff-bd814d300099

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceShiftedASummand_factor
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
end ErdosProblems.Erdos1049.PaperR12

open Polynomial
open scoped BigOperators
open PaperR11
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution {K : Type*} [Field K]
    (f : ℤ[X] →+* K) (n s j : ℕ) (hs : s ≤ 13 * n) (hj : j ≤ 14 * n)
    (hx : f X ≠ 0) :
    f (sourceShiftedASummand n s j) =
      f (sourceASummand n s) * (f X) ^ (-((j * (2 * n + s) : ℕ) : ℤ)) := by
  have h := congrArg f (sourceShiftedASummand_factor n s j hs hj)
  simp only [map_mul, map_pow] at h
  rw [zpow_neg, zpow_natCast]
  have hp : (f X) ^ (j * (2 * n + s)) ≠ 0 := pow_ne_zero _ hx
  apply mul_right_cancel₀ hp
  calc
    f (sourceShiftedASummand n s j) * (f X) ^ (j * (2 * n + s)) =
        f (sourceASummand n s) := by simpa only [mul_comm] using h
    _ = _ := by rw [mul_assoc, inv_mul_cancel₀ hp, mul_one]
