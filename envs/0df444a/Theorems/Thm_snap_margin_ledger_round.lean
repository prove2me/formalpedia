-- Prove2me | Theorems.Thm_snap_margin_ledger_round
-- name    : snap_margin_ledger_round
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:12:56.887281+00:00
-- url     : https://prove2.me/theorems/2322b260-ec08-40a8-a77a-df3af397d231
-- title:
--   Snap displacement versus the recorded margin (margin–ledger joint)
-- statement:
--   A separation loop that evaluates its oracle at a **snapped** (rational) centre, while its engine's recorded centre is the exact iterate, must account for the displacement when it records the round's margin.
--
--   Let $c$ be the cut normal, $a$ the snapped centre at which the oracle was evaluated, $a'$ the engine's recorded centre, and $S$ the feasible set. Two hypotheses bound the numerical data: $\lVert c\rVert \le C$ and $\lVert a-a'\rVert \le \text{eps}$.
--
--   **Main result.** If the cut separates $S$ around $a$ with margin $m$, i.e.
--   $$-m \le \langle c,\, z-a\rangle \qquad\text{for all } z\in S,$$
--   and $m>0$, $\text{eps}\ge 0$, $\rho\ge 0$, $\sigma\ge 0$, with the quadratic room $(\text{del})^2\le \rho^2\sigma$ satisfied at $\text{del} := m + C\,\text{eps}$, then all three ledger clauses hold:
--   $$0\le \text{del},\qquad (\text{del})^2\le \rho^2\sigma,\qquad -\text{del}\le \langle c,\, z-a'\rangle \ \text{ for all } z\in S.$$
--
--   The separation step is a two-term split and Cauchy–Schwarz:
--   $$\langle c, z-a'\rangle=\langle c, z-a\rangle+\langle c, a-a'\rangle\ \ge\ -m-\lVert c\rVert\,\lVert a-a'\rVert\ \ge\ -m-C\,\text{eps}.$$
--
--   **Why the sign matters.** The displacement can only *weaken* the guaranteed separation, so the recorded margin must be $m+C\,\text{eps}$ rather than $m-C\,\text{eps}$; a ledger that recorded the smaller value would accept rounds whose cut no longer separates the body. Equivalently: the quadratic room has to accommodate the snap cost on top of the oracle's own margin, which is exactly the bookkeeping constraint a numerical loop must satisfy to remain sound under finite-precision centres.
-- source:
--   Internal accounting lemma for the Quantum Max-Cut 0.53 formalisation (ellipsoid/separation loop ledger); elementary Cauchy–Schwarz argument, no external source.

import Mathlib
open Finset

theorem snap_margin_ledger_round {k : ℕ} {S : Set (Fin k → ℝ)} {c a a' : Fin k → ℝ} {m C eps rho sigma : ℝ}
    (hsep : ∀ z ∈ S, -m ≤ ∑ i, c i * (z i - a i))
    (hC : Real.sqrt (∑ i, (c i) ^ 2) ≤ C)
    (heps : Real.sqrt (∑ i, (a i - a' i) ^ 2) ≤ eps)
    (hm : 0 < m) (heps0 : 0 ≤ eps) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hroom : (m + C * eps) ^ 2 ≤ rho ^ 2 * sigma) :
    0 ≤ m + C * eps ∧ (m + C * eps) ^ 2 ≤ rho ^ 2 * sigma ∧
      ∀ z ∈ S, -(m + C * eps) ≤ ∑ i, c i * (z i - a' i) := by sorry
