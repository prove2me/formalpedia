-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR11.sourceA_factor
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:18:43.229997+00:00
-- url     : https://prove2.me/submissions/23ad1e36-fb52-4a5b-9281-772adfbef69a

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR11_sourceASummand_factor
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
# Actual finite 2004 A coefficient and its normalisation


The reindexing k = 14*n+1+s makes every exponent nonnegative. In particular
A is an actual integral polynomial, not a postulated source package.
This module proves the A-channel inclusion for every n, including n=0.
It does not assert the missing B-channel cancellation or the analytic source
identity. Those obligations are recorded separately, not hidden in a premise.
-/

namespace ErdosProblems.Erdos1049.PaperR11
open Polynomial
open scoped BigOperators
end ErdosProblems.Erdos1049.PaperR11

open Polynomial
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (n : ℕ) :
    sourceA n = X ^ sourceM n * sourceAWithoutMonomial n := by
  simp only [sourceA, sourceAWithoutMonomial, sourceASummand_factor,
    Finset.mul_sum]
