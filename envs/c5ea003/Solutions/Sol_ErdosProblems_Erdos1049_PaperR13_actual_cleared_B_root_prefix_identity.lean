-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR13.actual_cleared_B_root_prefix_identity
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:35:51.849635+00:00
-- url     : https://prove2.me/submissions/ca070065-e5ee-4103-bf60-b03334410405

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
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootBlocksR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceOmegaCancellationR13
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceDQuotient_factor
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceShiftedASummand_factor
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_root_power_reduce
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_finite_prefix_supported_on_multiples
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
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators
variable {K : Type*} [Field K]
lemma root_power_ne_one_of_not_dvd (q : K) {ell j : ℕ} (hell : 0 < ell)
    (hroot : q ^ ell = 1)
    (hprimitive : ∀ a : ℕ, 0 < a → a < ell → q ^ a ≠ 1)
    (hdiv : ¬ ell ∣ j) : q ^ j ≠ 1 := by
  rw [root_power_reduce q hroot j]
  apply hprimitive _ _ (Nat.mod_lt _ hell)
  have hm : j % ell ≠ 0 := fun h => hdiv (Nat.dvd_of_mod_eq_zero h)
  omega
lemma sourceD_eval_zero_at_root (q : K) (n ell : ℕ) (hell : 0 < ell)
    (helln : ell ≤ 15 * n) (hroot : q ^ ell = 1) :
    (sourceD n).eval₂ (Int.castRingHom K) q = 0 := by
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom K) q)
    (sourceDQuotient_factor n ell hell helln)
  simpa only [eval₂_mul, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one,
    hroot, sub_self, zero_mul] using h.symm
lemma sourceDQuotient_eval_zero_of_not_dvd (q : K) (n ell j : ℕ)
    (hell : 0 < ell) (helln : ell ≤ 15 * n) (hroot : q ^ ell = 1)
    (hprimitive : ∀ a : ℕ, 0 < a → a < ell → q ^ a ≠ 1)
    (hj0 : 0 < j) (hjn : j ≤ 15 * n) (hdiv : ¬ ell ∣ j) :
    (sourceDQuotient n j).eval₂ (Int.castRingHom K) q = 0 := by
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom K) q)
    (sourceDQuotient_factor n j hj0 hjn)
  simp only [eval₂_mul, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one,
    sourceD_eval_zero_at_root q n ell hell helln hroot] at h
  exact (mul_eq_zero.mp h).resolve_left
    (sub_ne_zero.mpr (root_power_ne_one_of_not_dvd q hell hroot hprimitive hdiv))
lemma sourceShiftedASummand_eval_eq_of_dvd (q : K) (n ell s j : ℕ)
    (hroot : q ^ ell = 1) (hs : s ≤ 13 * n) (hj : j ≤ 14 * n)
    (hdiv : ell ∣ j) :
    (sourceShiftedASummand n s j).eval₂ (Int.castRingHom K) q =
      (sourceASummand n s).eval₂ (Int.castRingHom K) q := by
  have hp : q ^ j = 1 := by
    obtain ⟨b, rfl⟩ := hdiv
    rw [pow_mul, hroot, one_pow]
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom K) q)
    (sourceShiftedASummand_factor n s j hs hj)
  simpa only [eval₂_mul, eval₂_pow, eval₂_X, pow_mul, hp, one_pow, one_mul] using h
lemma sourceDQuotient_eval_prefix (q : K) (n ell J : ℕ)
    (hell : 0 < ell) (helln : ell ≤ 15 * n) (hroot : q ^ ell = 1)
    (hprimitive : ∀ a : ℕ, 0 < a → a < ell → q ^ a ≠ 1)
    (hJ : J ≤ 15 * n) :
    (∑ j ∈ Icc 1 J, (sourceDQuotient n j).eval₂ (Int.castRingHom K) q) =
      sourcePolePrefix q n ell (J / ell) := by
  apply finite_prefix_supported_on_multiples _ ell J hell
  intro j hj hdiv
  obtain ⟨hj0, hjJ⟩ := mem_Icc.mp hj
  exact sourceDQuotient_eval_zero_of_not_dvd q n ell j hell helln hroot hprimitive
    hj0 (hjJ.trans hJ) hdiv
end ErdosProblems.Erdos1049.PaperR13

open ErdosProblems
open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators
variable {K : Type*} [Field K]
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR13 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution (q : K) (n ell : ℕ)
    (hell : 0 < ell) (helln : ell ≤ 15 * n) (hroot : q ^ ell = 1)
    (hprimitive : ∀ a : ℕ, 0 < a → a < ell → q ^ a ≠ 1) :
    (sourceClearedB n).eval₂ (Int.castRingHom K) q =
      ∑ s ∈ range (13 * n + 1),
        (sourceASummand n s).eval₂ (Int.castRingHom K) q *
          (sourcePolePrefix q n ell ((2 * n + s) / ell) +
            sourcePolePrefix q n ell (14 * n / ell)) := by
  classical
  let f : ℤ[X] →+* K := Polynomial.eval₂RingHom (Int.castRingHom K) q
  change f (sourceClearedB n) = _
  unfold sourceClearedB
  rw [map_sum]
  apply sum_congr rfl
  intro s hs
  have hs' : s ≤ 13 * n := by have := mem_range.mp hs; omega
  have hshift : (∑ j ∈ Icc 1 (14 * n), f (sourceShiftedASummand n s j * sourceDQuotient n j)) =
      ∑ j ∈ Icc 1 (14 * n), f (sourceASummand n s * sourceDQuotient n j) := by
    apply sum_congr rfl
    intro j hj
    obtain ⟨hj0, hjn⟩ := mem_Icc.mp hj
    rw [map_mul, map_mul]
    by_cases hdiv : ell ∣ j
    · rw [show f (sourceShiftedASummand n s j) = f (sourceASummand n s) from
        sourceShiftedASummand_eval_eq_of_dvd q n ell s j hroot hs' hjn hdiv]
    · have hz : f (sourceDQuotient n j) = 0 :=
        sourceDQuotient_eval_zero_of_not_dvd q n ell j hell helln hroot hprimitive
          hj0 (by omega) hdiv
      rw [hz, mul_zero, mul_zero]
  rw [map_add, map_sum, map_sum, hshift]
  simp only [map_mul, ← mul_sum]
  rw [show (∑ j ∈ Icc 1 (2 * n + s), f (sourceDQuotient n j)) =
      sourcePolePrefix q n ell ((2 * n + s) / ell) from
        sourceDQuotient_eval_prefix q n ell (2 * n + s) hell helln hroot hprimitive (by omega),
    show (∑ j ∈ Icc 1 (14 * n), f (sourceDQuotient n j)) =
      sourcePolePrefix q n ell (14 * n / ell) from
        sourceDQuotient_eval_prefix q n ell (14 * n) hell helln hroot hprimitive (by omega)]
  exact (mul_add _ _ _).symm
