-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR13.gaussian_field_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:06:33.780495+00:00
-- url     : https://prove2.me/submissions/fb8da8dc-8dc4-4c98-b12f-f0a5aa9aec4e

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_RootUnityLocalCancellationR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBTopDegreeR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootCarriesR13
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_succ
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_gaussian_polynomial_symmetry
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

section
open scoped BigOperators
open Finset Polynomial
namespace ErdosProblems.Erdos1049
variable {R : Type*} [CommRing R]
lemma eval₂_gaussBinom (q : R) : ∀ n k,
    eval₂ (Int.castRingHom R) q (gaussBinom (X : ℤ[X]) n k) = gaussBinom q n k
  | 0, 0 => by simp [gaussBinom]
  | 0, k + 1 => by simp [gaussBinom]
  | n + 1, 0 => by simp [gaussBinom]
  | n + 1, k + 1 => by
      rw [gaussBinom_succ, gaussBinom_succ, eval₂_add]
      split_ifs with h
      · rw [eval₂_mul, eval₂_pow, eval₂_X, eval₂_gaussBinom q n (k + 1),
          eval₂_gaussBinom q n k]
      · rw [eval₂_zero, eval₂_gaussBinom q n (k + 1)]
end ErdosProblems.Erdos1049
end

namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12
open scoped BigOperators
variable {K : Type*} [Field K]
end ErdosProblems.Erdos1049.PaperR13

open ErdosProblems
open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12
open scoped BigOperators
variable {K : Type*} [Field K]
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR13 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution (q : K) (n k : ℕ) (hk : k ≤ n) :
    gaussBinom q n k = gaussBinom q n (n - k) := by
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom K) q)
    (gaussian_polynomial_symmetry n k hk)
  simpa only [eval₂_gaussBinom] using h
