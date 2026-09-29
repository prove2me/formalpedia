-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_CoefficientDivisorFence_no_jump_through_fence
-- name    : ErdosProblems.Erdos243.CoefficientDivisorFence.no_jump_through_fence
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:46:17.632193+00:00
-- url     : https://prove2.me/theorems/5669acce-8f1e-46eb-9014-f7357bc744b2
-- title:
--   An exact step cannot jump across a divisor-covered interval
-- statement:
--   Let positive v and integer u satisfy ρ≥1, ρv≤u+B and ρv=au−bL, where B≥0. Suppose u<z+B, z>B, and every integer in [z,z+B) has a divisor m>B that also divides L. Then v<z+B.
-- source:
--   Pinned original Lean theorem and proof: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/CoefficientDivisorFence.lean#L28-L57
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

theorem ErdosProblems.Erdos243.CoefficientDivisorFence.no_jump_through_fence (a b L u v rho B z : ℤ)
    (hv : 0 < v) (hrho : 1 ≤ rho) (_hB : 0 ≤ B)
    (hcap : rho * v ≤ u + B)
    (hstep : rho * v = a * u - b * L)
    (hz : B < z) (hbefore : u < z + B)
    (hcover : ∀ x : ℤ, z ≤ x → x < z + B →
      ∃ m : ℤ, B < m ∧ m ∣ x ∧ m ∣ L) :
    v < z + B := by sorry
