-- Prove2me | solution 1 for LWEOperational.expectation_sub_le_l1Gap
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:45:55.277626+00:00
-- url     : https://prove2.me/submissions/82d64b51-79bd-41c4-9bb4-d8d979036918

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

theorem solution {Ω : Type*} [Fintype Ω]
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

#print axioms solution
