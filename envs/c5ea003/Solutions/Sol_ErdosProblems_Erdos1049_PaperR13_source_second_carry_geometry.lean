-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR13.source_second_carry_geometry
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:48:25.991809+00:00
-- url     : https://prove2.me/submissions/2b1ae204-1b92-4c07-a904-d622af679320

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

namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12
open scoped BigOperators
lemma source_add_div (a b n ell : ℕ) (hell : 0 < ell) :
    ((a + b) * n) / ell = a * n / ell + b * n / ell +
      if ell ≤ (a * n) % ell + (b * n) % ell then 1 else 0 := by
  rw [add_mul]
  exact Nat.add_div hell
lemma source_add_mod (a b n ell : ℕ) :
    ((a + b) * n) % ell =
      (a * n) % ell + (b * n) % ell -
        if (a * n) % ell + (b * n) % ell < ell then 0 else ell := by
  rw [add_mul]
  exact Nat.add_mod_eq_sub
end ErdosProblems.Erdos1049.PaperR13

open ErdosProblems
open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR13 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution (n ell : ℕ) (hell : 0 < ell)
    (hfirst : sourceCarryOne n ell ≤ 0) (hsecond : sourceCarryTwo n ell = 1) :
    (12 * n) % ell + n % ell = (13 * n) % ell ∧
    ell ≤ (13 * n) % ell + n % ell ∧
    (14 * n) % ell + n % ell < ell ∧
    (14 * n) % ell + ell = (13 * n) % ell + n % ell := by
  have h13 := source_add_div 12 1 n ell hell
  have h14 := source_add_div 13 1 n ell hell
  have h15 := source_add_div 14 1 n ell hell
  norm_num only [one_mul] at h13 h14 h15
  unfold sourceCarryOne at hfirst
  unfold sourceCarryTwo at hsecond
  have hcarry : ell ≤ (13 * n) % ell + n % ell := by
    split_ifs at h14 h15 <;> omega
  have hncarry : (14 * n) % ell + n % ell < ell := by
    split_ifs at h14 h15 <;> omega
  have hlow : (12 * n) % ell + n % ell < ell := by
    split_ifs at h13 h14 h15 <;> omega
  have hm13 := source_add_mod 12 1 n ell
  have hm14 := source_add_mod 13 1 n ell
  norm_num only [one_mul] at hm13 hm14
  rw [if_pos hlow, Nat.sub_zero] at hm13
  rw [if_neg (not_lt.mpr hcarry)] at hm14
  exact ⟨hm13.symm, hcarry, hncarry, by omega⟩
