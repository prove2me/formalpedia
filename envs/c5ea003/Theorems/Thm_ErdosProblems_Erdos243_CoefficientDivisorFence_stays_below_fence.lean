-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_CoefficientDivisorFence_stays_below_fence
-- name    : ErdosProblems.Erdos243.CoefficientDivisorFence.stays_below_fence
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:46:17.140977+00:00
-- url     : https://prove2.me/theorems/a928a2c4-6479-4dcb-a752-8da9f216704f
-- title:
--   A persistent divisor cover fences every later state
-- statement:
--   For a positive integer sequence U with pointwise factors ρ_n≥1, cap ρ_n U_(n+1)≤U_n+B, and exact step ρ_n U_(n+1)=a_n U_n−b_n L_n, suppose U_0<z+B, B≥0, z>B, and every integer in [z,z+B) has a divisor greater than B common to L_n at each n. Then U_n<z+B for every n.
-- source:
--   Pinned original Lean theorem and proof: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/CoefficientDivisorFence.lean#L59-L77
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested.

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

open ErdosProblems.Erdos243.CoefficientDivisorFence

theorem ErdosProblems.Erdos243.CoefficientDivisorFence.stays_below_fence
    (a b L U rho : ℕ → ℤ) (B z : ℤ)
    (hU : ∀ n, 0 < U n)
    (hrho : ∀ n, 1 ≤ rho n)
    (hB : 0 ≤ B) (hz : B < z)
    (hcap : ∀ n, rho n * U (n + 1) ≤ U n + B)
    (hstep : ∀ n, rho n * U (n + 1) = a n * U n - b n * L n)
    (hstart : U 0 < z + B)
    (hcover : ∀ n, ∀ x : ℤ, z ≤ x → x < z + B →
      ∃ m : ℤ, B < m ∧ m ∣ x ∧ m ∣ L n) :
    ∀ n, U n < z + B := by sorry
