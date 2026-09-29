-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.sourceASummandDegree_succ
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:19:50.795043+00:00
-- url     : https://prove2.me/submissions/7676336f-2b2e-4657-a42a-10fb6088fec7

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Theorems.Thm_ErdosProblems_Erdos1049_choose_two_succ
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
theorem solution (n s : ℕ) (hs : s < 13 * n) :
    sourceASummandDegree n (s + 1) = sourceASummandDegree n s + (26 * n - s) := by
  have hsub : 13 * n - (s + 1) + 1 = 13 * n - s := by omega
  have hsub2 : 26 * n - s + s = 26 * n := by omega
  unfold sourceASummandDegree sourceAExponent
  rw [choose_two_succ]
  rw [← hsub, ← hsub2]
  ring_nf
  omega
