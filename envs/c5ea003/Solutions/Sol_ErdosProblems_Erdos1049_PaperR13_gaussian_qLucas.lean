-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR13.gaussian_qLucas
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:18:24.20173+00:00
-- url     : https://prove2.me/submissions/48ec64a8-38b6-4b09-a3cd-cf21a3064f88

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_RootUnityLocalCancellationR13
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_eq_zero_of_lt
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_self
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_succ_of_le
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_right
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_gaussian_first_root_block_zero
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_quotient_remainder_successor_carry
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_quotient_remainder_successor_no_carry
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_root_power_reduce
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

namespace ErdosProblems.Erdos1049.PaperR13
variable {K : Type*} [Field K]
lemma root_power_difference (q : K) (hq : q ≠ 0) {ell n k : ℕ}
    (hroot : q ^ ell = 1) (hk : k ≤ n) (hrem : k % ell ≤ n % ell) :
    q ^ (n - k) = q ^ (n % ell - k % ell) := by
  apply mul_right_cancel₀ (pow_ne_zero (k % ell) hq)
  calc
    q ^ (n - k) * q ^ (k % ell) = q ^ (n - k) * q ^ k := by
      rw [root_power_reduce q hroot k]
    _ = q ^ n := by rw [← pow_add, Nat.sub_add_cancel hk]
    _ = q ^ (n % ell) := root_power_reduce q hroot n
    _ = q ^ (n % ell - k % ell) * q ^ (k % ell) := by
      rw [← pow_add, Nat.sub_add_cancel hrem]
lemma lucas_expression_zero_of_lt (q : K) {ell n k : ℕ}
    (hnk : n < k) :
    ((n / ell).choose (k / ell) : K) * gaussBinom q (n % ell) (k % ell) = 0 := by
  have hd : n / ell ≤ k / ell := Nat.div_le_div_right hnk.le
  rcases lt_or_eq_of_le hd with hlt | heq
  · rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, zero_mul]
  · have hn := Nat.mod_add_div n ell
    have hk := Nat.mod_add_div k ell
    rw [heq] at hn
    have hrem : n % ell < k % ell := by omega
    rw [gaussBinom_eq_zero_of_lt q hrem, mul_zero]
end ErdosProblems.Erdos1049.PaperR13

open ErdosProblems
open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.PaperR13
variable {K : Type*} [Field K]
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR13 in
set_option maxHeartbeats 1000000 in

theorem solution (q : K) (hq : q ≠ 0) {ell : ℕ} (hell : 0 < ell)
    (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1) :
    ∀ n k : ℕ, gaussBinom q n k =
      ((n / ell).choose (k / ell) : K) * gaussBinom q (n % ell) (k % ell) := by
  intro n
  induction n with
  | zero =>
      intro k
      rcases k with _ | k
      · simp
      · rw [gaussBinom_zero_succ]
        exact (lucas_expression_zero_of_lt q (ell := ell) (by omega)).symm
  | succ n ih =>
      intro k
      rcases k with _ | k
      · simp
      · by_cases hk : k ≤ n
        · rw [gaussBinom_succ_of_le q hk, ih (k + 1), ih k]
          have hnlt := Nat.mod_lt n hell
          have hklt := Nat.mod_lt k hell
          by_cases hnc : n % ell + 1 = ell
          · obtain ⟨hnd, hnm⟩ := quotient_remainder_successor_carry hell hnc
            have hnrem : n % ell = ell - 1 := by omega
            by_cases hkc : k % ell + 1 = ell
            · obtain ⟨hkd, hkm⟩ := quotient_remainder_successor_carry hell hkc
              have hkrem : k % ell = ell - 1 := by omega
              have hpow := root_power_difference q hq hroot hk
                (show k % ell ≤ n % ell by omega)
              rw [hnrem, hkrem, Nat.sub_self, pow_zero] at hpow
              rw [hnd, hnm, hkd, hkm, hpow, hnrem, hkrem]
              simp [gaussBinom_self, Nat.choose_succ_succ, Nat.cast_add, add_comm]
            · obtain ⟨hkd, hkm⟩ := quotient_remainder_successor_no_carry hell (by omega : k % ell + 1 < ell)
              have hrem : k % ell ≤ n % ell := by omega
              have hpow := root_power_difference q hq hroot hk hrem
              have hz : gaussBinom q (n % ell) (k % ell + 1) +
                  q ^ (n % ell - k % ell) * gaussBinom q (n % ell) (k % ell) = 0 := by
                rw [← gaussBinom_succ_of_le q hrem, hnc]
                exact gaussian_first_root_block_zero q hroot hprimitive (by omega) (by omega)
              rw [hnd, hnm, hkd, hkm, hpow, gaussBinom_zero_succ, mul_zero]
              calc
                _ = ((n / ell).choose (k / ell) : K) *
                    (gaussBinom q (n % ell) (k % ell + 1) +
                      q ^ (n % ell - k % ell) * gaussBinom q (n % ell) (k % ell)) := by ring
                _ = 0 := by rw [hz, mul_zero]
          · obtain ⟨hnd, hnm⟩ := quotient_remainder_successor_no_carry hell (by omega : n % ell + 1 < ell)
            by_cases hkc : k % ell + 1 = ell
            · obtain ⟨hkd, hkm⟩ := quotient_remainder_successor_carry hell hkc
              have hz : gaussBinom q (n % ell) (k % ell) = 0 :=
                gaussBinom_eq_zero_of_lt q (by omega)
              rw [hnd, hnm, hkd, hkm, hz]
              simp
            · obtain ⟨hkd, hkm⟩ := quotient_remainder_successor_no_carry hell (by omega : k % ell + 1 < ell)
              rw [hnd, hnm, hkd, hkm]
              by_cases hrem : k % ell ≤ n % ell
              · rw [root_power_difference q hq hroot hk hrem,
                  gaussBinom_succ_of_le q hrem]
                ring
              · have hlt : n % ell < k % ell := by omega
                rw [gaussBinom_eq_zero_of_lt q hlt,
                  gaussBinom_eq_zero_of_lt q (by omega : n % ell < k % ell + 1),
                  gaussBinom_eq_zero_of_lt q (by omega : n % ell + 1 < k % ell + 1)]
                ring
        · have hlt : n + 1 < k + 1 := by omega
          rw [gaussBinom_eq_zero_of_lt q hlt]
          exact (lucas_expression_zero_of_lt q hlt).symm
