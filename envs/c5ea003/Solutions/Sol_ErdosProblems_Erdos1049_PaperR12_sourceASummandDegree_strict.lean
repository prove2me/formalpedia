-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.sourceASummandDegree_strict
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:21:46.218103+00:00
-- url     : https://prove2.me/submissions/5c8ccc11-5f1f-4beb-9f79-0821b3ea00e7

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceASummandDegree_succ
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
# Exact Gaussian and actual A degrees


The unique highest summand is proved at every index; finite reconstructions
are not used to infer a polynomial identity. The integer coefficient mass of
each Gaussian is also evaluated exactly, rather than bounding one coefficient
and silently treating that as an l1 bound.
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
theorem solution (n : ℕ) {s t : ℕ}
    (hst : s < t) (ht : t ≤ 13 * n) :
    sourceASummandDegree n s < sourceASummandDegree n t := by
  induction t with
  | zero => omega
  | succ t ih =>
      have ht' : t < 13 * n := by omega
      have hstep : sourceASummandDegree n t < sourceASummandDegree n (t + 1) := by
        rw [sourceASummandDegree_succ n t ht']
        have hpos : 0 < 26 * n - t := by omega
        omega
      rcases Nat.lt_succ_iff_lt_or_eq.mp hst with hst' | rfl
      · exact (ih hst' (by omega)).trans hstep
      · exact hstep
