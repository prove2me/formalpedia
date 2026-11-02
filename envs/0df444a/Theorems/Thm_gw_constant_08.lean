-- Prove2me | Theorems.Thm_gw_constant_08
-- name    : gw_constant_08
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T22:47:53.686328+00:00
-- url     : https://prove2.me/theorems/18a04d9c-898f-4687-9079-5c2bf0313027
-- title:
--   Goemans–Williamson constant, slack form: $2\\arccos t \\ge \\frac45\\pi(1-t)$
-- statement:
--   The Goemans–Williamson scalar inequality with the comfortable constant $4/5$.
--
--   For every $t \in [-1, 1]$,
--   $$\frac{4}{5}\,\pi\,(1-t) \;\le\; 2\arccos t,$$
--   i.e. the per-edge ratio $2\arccos t / (\pi(1-t))$ is at least $0.8$.
--
--   **Role.** In Goemans–Williamson rounding of a MaxCut (or Quantum Max-Cut cut-state) SDP solution, an edge whose vertex vectors have inner product $t$ is cut with probability $\arccos(t)/\pi$, while the SDP objective counts $w(1-t)/2$ per edge; this one-variable inequality converts the arccos expectation into the approximation guarantee. The optimal constant is $\alpha_{GW} = \min_t 2\arccos t/(\pi(1-t)) \approx 0.8785671$; the rational $4/5$ is a deliberately comfortable slack, placed at the distance where the derivative sign changes are decidable with rational split points.
--
--   **Formalization Note.** Statement over `Real.arccos` (principal branch $[0,\pi]$); no analytic hypotheses beyond $t \in [-1,1]$.
-- source:
--   Michel X. Goemans and David P. Williamson, Improved Approximation Algorithms for Maximum Cut and Satisfiability Problems Using Semidefinite Programming, J. ACM 42 (1995), https://doi.org/10.1145/227683.227684 , Section 3; slack constant 4/5 chosen for a fully rational proof (split points 3/5, 5/8)

import Mathlib

theorem gw_constant_08 (t : ℝ) (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    (4 / 5 : ℝ) * Real.pi * (1 - t) ≤ 2 * Real.arccos t := by sorry
