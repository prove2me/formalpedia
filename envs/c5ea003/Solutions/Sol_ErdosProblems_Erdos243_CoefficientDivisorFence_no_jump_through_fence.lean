-- Prove2me | solution 1 for ErdosProblems.Erdos243.CoefficientDivisorFence.no_jump_through_fence
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:46:36.671627+00:00
-- url     : https://prove2.me/submissions/1eb4b071-19cc-44db-9f5f-6058cfa63d02

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

namespace ErdosProblems.Erdos243.CoefficientDivisorFence
/-- A persistent divisor of the state and clearing denominator divides the
jump, independently of the integral forcing coefficient. -/
theorem divides_jump (a b L u v m : ℤ)
    (hstep : v = a * u - b * L)
    (hu : m ∣ u) (hL : m ∣ L) : m ∣ v - u := by
  have hrewrite : v - u = (a - 1) * u - b * L := by
    rw [hstep]
    ring
  rw [hrewrite]
  exact dvd_sub (dvd_mul_of_dvd_right hu (a - 1)) (dvd_mul_of_dvd_right hL b)
end ErdosProblems.Erdos243.CoefficientDivisorFence

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.CoefficientDivisorFence in
theorem solution (a b L u v rho B z : ℤ)
    (hv : 0 < v) (hrho : 1 ≤ rho) (_hB : 0 ≤ B)
    (hcap : rho * v ≤ u + B)
    (hstep : rho * v = a * u - b * L)
    (hz : B < z) (hbefore : u < z + B)
    (hcover : ∀ x : ℤ, z ≤ x → x < z + B →
      ∃ m : ℤ, B < m ∧ m ∣ x ∧ m ∣ L) :
    v < z + B := by
  by_contra hnot
  have hafter : z + B ≤ v := by omega
  have hrhoone : rho = 1 := by
    by_contra hne
    have htwo : (2 : ℤ) ≤ rho := by omega
    have htwov : 2 * v ≤ rho * v := by nlinarith
    have hdrop : 2 * v ≤ u + B := by linarith
    have hzule : z ≤ u := by
      have : v ≤ rho * v := by nlinarith
      omega
    nlinarith
  have hstep' : v = a * u - b * L := by simpa [hrhoone] using hstep
  have hcap' : v ≤ u + B := by simpa [hrhoone] using hcap
  have hzu : z ≤ u := by omega
  obtain ⟨m, hm, hmu, hmL⟩ := hcover u hzu hbefore
  have hd : 0 < v - u := by omega
  have hdiv : m ∣ v - u := divides_jump a b L u v m hstep' hmu hmL
  have hle : m ≤ v - u := Int.le_of_dvd hd hdiv
  omega
