-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
-- name    : ErdosProblems_Erdos1049_SourcePolynomialR11
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:46:15.931258+00:00
-- url     : https://prove2.me/theorems/6c6211d4-ae3a-40db-af5a-0f08f207c40a
-- title:
--   Actual finite 2004 A coefficient and its normalisation
-- statement:
--   Reindexing the 2004 coefficient makes all A exponents nonnegative, constructing an actual integral A polynomial and its source normalization for every n. The submitted module contains the source declarations sourceM, sourceAExponent, sourceGaussianProduct, sourceNormalisedASummand, sourceASummand, among others. Source topic: Actual finite 2004 A coefficient and its normalisation.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourcePolynomialR11.lean#L20-L187
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
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

/-- The exact published normalising exponent. -/
def sourceM (n : ℕ) : ℕ := 266 * n ^ 2 + 34 * n + 1

/-- The exponent left after X^M is removed from the s-th actual A summand. -/
def sourceAExponent (n s : ℕ) : ℕ :=
  2 * n ^ 2 + (n + 1) * s + s.choose 2

noncomputable def sourceGaussianProduct (n s : ℕ) : ℤ[X] :=
  gaussBinom X (14 * n + s) (12 * n) *
    gaussBinom X (13 * n) (13 * n - s)

noncomputable def sourceNormalisedASummand (n s : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ s) * X ^ sourceAExponent n s * sourceGaussianProduct n s

/-- The unnormalised coefficient, equal to the literal source after reindexing. -/
noncomputable def sourceASummand (n s : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ s) * X ^ (sourceM n + sourceAExponent n s) *
    sourceGaussianProduct n s

noncomputable def sourceA (n : ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range (13 * n + 1), sourceASummand n s

noncomputable def sourceAWithoutMonomial (n : ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range (13 * n + 1), sourceNormalisedASummand n s





















noncomputable def sourceWeight (n l : ℕ) : ℤ :=
  PaperR7.omegaWeight ((n : ℝ) / (l : ℝ))





noncomputable def sourceD (n : ℕ) : ℤ[X] :=
  ∏ l ∈ Finset.Icc 1 (15 * n), cyclotomic l ℤ

/-- Including l=1 is harmless: its weight is omega(n)=0. -/
noncomputable def sourceOmega (n : ℕ) : ℤ[X] :=
  ∏ l ∈ Finset.Icc 1 (15 * n), (cyclotomic l ℤ) ^ (sourceWeight n l).toNat

noncomputable def sourceComplement (n : ℕ) : ℤ[X] :=
  ∏ l ∈ Finset.Icc 1 (15 * n),
    if sourceWeight n l = 0 then cyclotomic l ℤ else 1



noncomputable def sourceU (n : ℕ) : ℤ[X] :=
  sourceComplement n * sourceAWithoutMonomial n





end ErdosProblems.Erdos1049.PaperR11


