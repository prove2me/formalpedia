-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.sourceInnerZ_qPochhammer
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:54:02.46754+00:00
-- url     : https://prove2.me/submissions/40720d83-af55-4550-a5ab-c8c8795b03ef

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_mul_qPochhammer
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_eq_sum
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-! # The missing free-variable finite source transform
The variable z is independent of q.
Consequently the identity can be specialised in any commutative ring,
including a Laurent polynomial ring; it is not limited to z=q^alpha with
alpha a natural number. The proof uses only two finite q-binomial expansions.
-/

namespace ErdosProblems.Erdos1049.PaperR12
open Finset
open scoped BigOperators
variable {R : Type*} [CommRing R]
end ErdosProblems.Erdos1049.PaperR12

open Finset
open scoped BigOperators
variable {R : Type*} [CommRing R]
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
set_option maxHeartbeats 500000 in

theorem solution (q z : R) {a d v : ℕ}
    (ha : 1 ≤ a) (hv : 1 ≤ v) :
    qPochhammer q q (a - 1) * sourceInnerZ q z a d v =
      ∑ h ∈ range a,
        (-1 : R) ^ h * q ^ (h * (d + 1) + h.choose 2) *
          gaussBinom q (a - 1) h * qPochhammer q (z * q ^ h) (v - 1) := by
  unfold sourceInnerZ
  rw [mul_sum]
  have hleft :
      (∑ j ∈ range v,
        qPochhammer q q (a - 1) *
          ((-1 : R) ^ j * q ^ j.choose 2 * z ^ j *
            gaussBinom q (v - 1) j * gaussBinom q (a + d + j - 1) (a - 1))) =
      ∑ j ∈ range v,
        (-1 : R) ^ j * q ^ j.choose 2 * z ^ j * gaussBinom q (v - 1) j *
          qPochhammer q (q ^ (d + j + 1)) (a - 1) := by
    apply sum_congr rfl
    intro j hj
    have hle : a - 1 ≤ a + d + j - 1 := by omega
    have hidx : a + d + j - 1 - (a - 1) + 1 = d + j + 1 := by omega
    have hg := gaussBinom_mul_qPochhammer q hle
    rw [hidx] at hg
    rw [← hg]
    ring
  rw [hleft]
  have ha' : a - 1 + 1 = a := by omega
  have hv' : v - 1 + 1 = v := by omega
  have hexpand :
      (∑ j ∈ range v,
        (-1 : R) ^ j * q ^ j.choose 2 * z ^ j * gaussBinom q (v - 1) j *
          qPochhammer q (q ^ (d + j + 1)) (a - 1)) =
      ∑ j ∈ range v, ∑ h ∈ range a,
        (-1 : R) ^ j * q ^ j.choose 2 * z ^ j * gaussBinom q (v - 1) j *
          qBinomialTerm q (q ^ (d + j + 1)) (a - 1) h := by
    apply sum_congr rfl
    intro j hj
    rw [qPochhammer_eq_sum, ha', mul_sum]
  rw [hexpand, Finset.sum_comm]
  apply sum_congr rfl
  intro h hh
  have hterm (j : ℕ) :
      (-1 : R) ^ j * q ^ j.choose 2 * z ^ j * gaussBinom q (v - 1) j *
          qBinomialTerm q (q ^ (d + j + 1)) (a - 1) h =
      ((-1 : R) ^ h * q ^ (h * (d + 1) + h.choose 2) * gaussBinom q (a - 1) h) *
        qBinomialTerm q (z * q ^ h) (v - 1) j := by
    simp only [qBinomialTerm, pow_add, pow_mul, mul_pow, pow_one]
    ring
  simp_rw [hterm]
  rw [← mul_sum]
  have hp : (∑ j ∈ range v, qBinomialTerm q (z * q ^ h) (v - 1) j) =
      qPochhammer q (z * q ^ h) (v - 1) := by
    simpa only [hv'] using (qPochhammer_eq_sum q (z * q ^ h) (v - 1)).symm
  rw [hp]
