-- Prove2me | Theorems.Thm_gw_constant
-- name    : gw_constant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-01T19:15:09.193881+00:00
-- url     : https://prove2.me/theorems/ae8a2c61-3a88-42e3-9450-37623fcce87e
-- title:
--   Goemans–Williamson constant: $2\\arccos t \\ge 0.8785\\,\\pi(1-t)$
-- statement:
--   The Goemans–Williamson constant inequality.
--
--   For every $t \in [-1, 1]$,
--
--   $$\frac{8785}{10000}\,\pi\,(1 - t) \;\le\; 2\arccos t,$$
--
--   equivalently the ratio $\dfrac{2\arccos t}{\pi(1-t)}$ is at least $0.8785$.
--
--   **Role.** In Goemans–Williamson rounding of a MaxCut SDP solution, an edge whose vertex vectors have inner product $t$ is cut with probability $\arccos(t)/\pi$, while the SDP objective rho counts $w(1-t)/2$. This one-variable inequality is exactly the statement that the rounding loses no more than a factor $1/0.8785$; it is the analytic core of every arccos-based MaxCut/Quantum Max-Cut rounding analysis. The true optimal constant is $\alpha_{GW} = \min_{t} 2\arccos t/(\pi(1-t)) \approx 0.8785671$, so the statement with $0.8785$ is deliberately slightly slack.
--
--   **Formalization Note.** Stated for `Real.arccos` with the standard branch in $[0,\pi]$; no analytic hypotheses beyond $t \in [-1,1]$.
-- source:
--   Michel X. Goemans and David P. Williamson, Improved Approximation Algorithms for Maximum Cut and Satisfiability Problems Using Semidefinite Programming, J. ACM 42 (1995), https://doi.org/10.1145/227683.227684 , Section 3 (the constant 0.878567); the slightly slack rational 0.8785 is chosen so the statement has a strict rational margin

import Mathlib

theorem gw_constant (t : ℝ) (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    (8785 / 10000 : ℝ) * Real.pi * (1 - t) ≤ 2 * Real.arccos t := by sorry
