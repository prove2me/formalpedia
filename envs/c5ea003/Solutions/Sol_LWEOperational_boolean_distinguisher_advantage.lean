-- Prove2me | solution 1 for LWEOperational.boolean_distinguisher_advantage
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:45:55.801158+00:00
-- url     : https://prove2.me/submissions/b8e69a80-e2d4-48b5-b0af-f08cc8c5f250

-- Thm stub generated from Cryptography/LWE/OperationalSecurity.lean
import Mathlib
import Definitions.Def_Cryptography_LWE_OperationalSecurity

/-!
# Operational Statistical Security for LWE Hybrids

This file turns the `ℓ¹` game distance used by the finite LWE IND-CPA
formalization into an operational statement about every bounded distinguisher.
It also isolates the ring-theoretic uniformity fact used in ring-LWE hybrids:
multiplication by a unit, followed by addition of an error, permutes the ring.
-/

open Finset BigOperators

noncomputable section

open LWEOperational

theorem expectation_sub_le_l1Gap_aux {Ω : Type*} [Fintype Ω]
    (P Q : FinitePMF Ω) (test : Ω → ℝ)
    (htest : ∀ x, 0 ≤ test x ∧ test x ≤ 1) :
    |expectation P test - expectation Q test| ≤ l1Gap P Q := by
  rw [expectation, expectation, l1Gap, ← Finset.sum_sub_distrib]
  calc
    |∑ x, (P.mass x * test x - Q.mass x * test x)|
        ≤ ∑ x, |P.mass x * test x - Q.mass x * test x| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |P.mass x - Q.mass x| * |test x| := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← abs_mul]
          congr 1
          ring
    _ ≤ ∑ x, |P.mass x - Q.mass x| := by
          apply Finset.sum_le_sum
          intro x _
          rw [abs_of_nonneg (htest x).1]
          exact mul_le_of_le_one_right (abs_nonneg _) (htest x).2

theorem solution {Ω : Type*} [Fintype Ω]
    (P Q : FinitePMF Ω) (adversary : Ω → Bool) :
    |(∑ x with adversary x = true, P.mass x) -
      (∑ x with adversary x = true, Q.mass x)| ≤ l1Gap P Q := by
  let test : Ω → ℝ := fun x => if adversary x = true then 1 else 0
  have htest : ∀ x, 0 ≤ test x ∧ test x ≤ 1 := by
    intro x
    simp only [test]
    split_ifs <;> norm_num
  have h := expectation_sub_le_l1Gap_aux P Q test htest
  simpa [expectation, test, Finset.sum_filter] using h

#print axioms solution
