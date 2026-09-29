-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.source_shift_homogeneous_exponent
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:03:57.373918+00:00
-- url     : https://prove2.me/submissions/1c79d21d-47a1-4e1e-8ddb-07f9c3664388

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceHomogeneousBase_add
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
theorem solution (n s j u : ℕ)
    (hs : s ≤ 13 * n) (hj : j ≤ 14 * n) (hu : u < 13 * n) (hju : j = n + u + 1) :
    sourceM n + sourceAExponent n s - j * (2 * n + s) =
      sourceHomogeneousBase n j u + s.choose 2 + u * (13 * n - s) := by
  have hb := sourceHomogeneousBase_add n j u hj hu
  have hsub : 13 * n - s + s = 13 * n := by omega
  have hsubmul : u * (13 * n - s) + u * s = 13 * n * u := by
    calc
      _ = u * (13 * n - s + s) := by ring
      _ = _ := by rw [hsub]; ring
  have hprod : j * (2 * n + s) = (n + u + 1) * (2 * n + s) := by rw [hju]
  have hexact : sourceHomogeneousBase n j u + s.choose 2 + u * (13 * n - s) +
      j * (2 * n + s) = sourceM n + sourceAExponent n s := by
    unfold sourceAExponent
    nlinarith
  omega
