-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.homogeneousPochhammer_zero
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:46:45.35202+00:00
-- url     : https://prove2.me/submissions/8f58fdf3-069e-4ed4-bb26-1133dbd2fdd4

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
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
theorem solution (u h N : ℕ) (hu : u < N) (hh : h ≤ u) :
    homogeneousPochhammer (X : ℤ[X]) (X ^ u) h N = 0 := by
  unfold homogeneousPochhammer
  apply Finset.prod_eq_zero (Finset.mem_range.mpr (show u - h < N by omega))
  have he : h + (u - h) = u := by omega
  rw [he, sub_self]
