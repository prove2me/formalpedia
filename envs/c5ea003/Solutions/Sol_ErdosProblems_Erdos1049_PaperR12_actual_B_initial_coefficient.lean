-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.actual_B_initial_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:32:11.537813+00:00
-- url     : https://prove2.me/submissions/23ae1eb2-2c7e-4a8d-b0bb-494f205ffa8c

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_X_power_dvd_of_le
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_X_power_dvd_signed_summand
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_homogeneous_source_inner_dvd
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceHomogeneousBase_order
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceShiftedASum_homogeneous
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceClearedB_reordered
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_actual_middle_channel_initial
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
# Exact initial coefficient of the actual B numerator


The numerator is divisible by X^M but not X^(M+1): at every n>=1 its
coefficient at M is exactly 1. This is proved by isolating the actual j=n,
s=0 channel. No finite reconstruction or initial-order hypothesis is used.
-/

namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial PaperR11
open scoped BigOperators







lemma coefficient_zero_of_X_power_dvd (p : ℤ[X]) (m : ℕ)
    (h : (X : ℤ[X]) ^ (m + 1) ∣ p) : p.coeff m = 0 :=
  Polynomial.X_pow_dvd_iff.mp h m (by omega)

lemma sourceASummand_strict_monomial (n s : ℕ) (hn : 1 ≤ n) :
    (X : ℤ[X]) ^ (sourceM n + 1) ∣ sourceASummand n s := by
  unfold sourceASummand
  apply X_power_dvd_signed_summand
  unfold sourceAExponent
  nlinarith [Nat.zero_le ((n + 1) * s), Nat.zero_le (s.choose 2)]

lemma sourceShiftedASummand_strict_early (n s j : ℕ) (hn : 1 ≤ n) (hj : j < n) :
    (X : ℤ[X]) ^ (sourceM n + 1) ∣ sourceShiftedASummand n s j := by
  have hm := Nat.mul_le_mul_right (2 * n + s) (show j + 1 ≤ n by omega)
  have he : j * (2 * n + s) + 1 ≤ sourceAExponent n s := by
    unfold sourceAExponent
    nlinarith [Nat.zero_le (s.choose 2)]
  unfold sourceShiftedASummand
  apply X_power_dvd_signed_summand
  omega







/-- All late channels start strictly after M, not merely at M. -/
theorem actual_shifted_A_sum_strict_late (n j : ℕ)
    (hjn : n < j) (hj : j ≤ 14 * n) :
    (X : ℤ[X]) ^ (sourceM n + 1) ∣ sourceShiftedASum n j := by
  let u := j - n - 1
  have hu : u < 13 * n := by dsimp [u]; omega
  have hju : j = n + u + 1 := by dsimp [u]; omega
  obtain ⟨v, hv⟩ := homogeneous_source_inner_dvd n u hu
  rw [sourceShiftedASum_homogeneous n j u hj hu hju, hv, ← mul_assoc, ← pow_add]
  have he : sourceM n + 1 ≤ sourceHomogeneousBase n j u + sourceHomogeneousOrder n u := by
    rw [sourceHomogeneousBase_order n j u hj hu hju]
    omega
  exact dvd_mul_of_dvd_left (X_power_dvd_of_le _ _ he) v
end ErdosProblems.Erdos1049.PaperR12

open Polynomial PaperR11
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (sourceClearedB n).coeff (sourceM n) = 1 := by
  classical
  rw [sourceClearedB_reordered, coeff_add]
  have hfirst : (∑ s ∈ Finset.range (13 * n + 1),
      ∑ l ∈ Finset.Icc 1 (2 * n + s),
        sourceASummand n s * sourceDQuotient n l).coeff (sourceM n) = 0 := by
    apply coefficient_zero_of_X_power_dvd
    apply Finset.dvd_sum
    intro s hs
    apply Finset.dvd_sum
    intro l hl
    exact dvd_mul_of_dvd_left (sourceASummand_strict_monomial n s hn) _
  rw [hfirst, zero_add, finset_sum_coeff, Finset.sum_eq_single n]
  · exact actual_middle_channel_initial n hn
  · intro j hj hjn
    apply coefficient_zero_of_X_power_dvd
    apply dvd_mul_of_dvd_left
    rcases lt_or_gt_of_ne hjn with hlt | hgt
    · unfold sourceShiftedASum
      exact Finset.dvd_sum (fun s _ => sourceShiftedASummand_strict_early n s j hn hlt)
    · exact actual_shifted_A_sum_strict_late n j hgt (Finset.mem_Icc.mp hj).2
  · intro hnot
    exact (hnot (Finset.mem_Icc.mpr ⟨hn, by omega⟩)).elim
