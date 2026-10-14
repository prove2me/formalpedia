-- Prove2me | Theorems.Thm_weightedLogMassReal_odd_recip_le_three
-- name    : weightedLogMassReal_odd_recip_le_three
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-12T22:43:40.412021+00:00
-- url     : https://prove2.me/theorems/59550abb-0f0d-4df9-ac33-80dbdcec09a2
-- title:
--   Crude uniform bound for the odd reciprocal logarithmic mass
-- statement:
--   Let $E$ be any property of natural numbers and let $x \ge 2$ be real. Consider the logarithmically normalized reciprocal sum over positive odd integers $n \le x$ satisfying $E$:
--
--   $$\frac{1}{\log x}\sum_{\substack{1 \le n \le x,\ n\ \mathrm{odd},\ E(n)}} \frac{1}{n}.$$
--
--   This quantity is at most $3$, uniformly in $E$ and $x$.
--
--   The estimate is the trivial bounded-threshold input for the proof of Theorem 3.1 in Tao's paper: the full reciprocal sum over odd $n \le x$ is $O(\log x)$ by the harmonic bound $\sum_{n \le x} 1/n \le 1 + \log x$, so after normalization by $\log x$ every exceptional set has uniformly bounded mass. It disposes of bounded thresholds $N_0$ in Theorem 3.1, where no decay in $N_0$ is needed.
--
--   **Formalization Note** The sum is `weightedLogMassReal` with domain the positive odd integers, exceptional predicate $E$, and weight $1/n$ at real cutoff $x$.
-- source:
--   Auxiliary crude bound for Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7, Section 3, proof of Theorem 3.1 (bounded thresholds are trivial). Harmonic estimate is standard. https://arxiv.org/html/1909.03562v7

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_weightedLogMassReal

theorem weightedLogMassReal_odd_recip_le_three (E : ℕ → Prop) (x : ℝ) (hx : 2 ≤ x) :
    weightedLogMassReal (fun n => 0 < n ∧ Odd n) E (fun n => 1 / (n : ℝ)) x ≤ 3 := by sorry
