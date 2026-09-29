-- Prove2me | solution 1 for ErdosProblems.Erdos243.CoefficientDivisorFence.stays_below_fence
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:48:12.008479+00:00
-- url     : https://prove2.me/submissions/8c114114-cc6c-405d-bd43-cf995f98d5cb

import Theorems.Thm_ErdosProblems_Erdos243_CoefficientDivisorFence_no_jump_through_fence
import Mathlib.Tactic

namespace ErdosProblems.Erdos243.CoefficientDivisorFence
end ErdosProblems.Erdos243.CoefficientDivisorFence

/-!
# Coefficient-independent divisor fences (r5)

Finite transition algebra only.  This module does not claim the global CRT
supply theorem, the analytic positive-numerator transfer, or the Erdős #243
endpoint.  The covering hypothesis is explicit: producing such a cover is a
separate CRT argument, and producing the required old divisors is a separate
record argument.

Not imported into `ErdosProblems/Root.lean`.  Erdős #243 remains open.
-/

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.CoefficientDivisorFence in
theorem solution
    (a b L U rho : ℕ → ℤ) (B z : ℤ)
    (hU : ∀ n, 0 < U n)
    (hrho : ∀ n, 1 ≤ rho n)
    (hB : 0 ≤ B) (hz : B < z)
    (hcap : ∀ n, rho n * U (n + 1) ≤ U n + B)
    (hstep : ∀ n, rho n * U (n + 1) = a n * U n - b n * L n)
    (hstart : U 0 < z + B)
    (hcover : ∀ n, ∀ x : ℤ, z ≤ x → x < z + B →
      ∃ m : ℤ, B < m ∧ m ∣ x ∧ m ∣ L n) :
    ∀ n, U n < z + B := by
  intro n
  induction n with
  | zero => exact hstart
  | succ n ih =>
      exact no_jump_through_fence (a n) (b n) (L n) (U n) (U (n + 1))
        (rho n) B z (hU (n + 1)) (hrho n) hB (hcap n) (hstep n)
        hz ih (hcover n)
