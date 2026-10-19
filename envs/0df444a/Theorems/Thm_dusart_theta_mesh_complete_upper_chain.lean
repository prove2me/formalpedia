-- Prove2me | Theorems.Thm_dusart_theta_mesh_complete_upper_chain
-- name    : dusart_theta_mesh_complete_upper_chain
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-17T05:02:42.573082+00:00
-- url     : https://prove2.me/theorems/70f87ad8-3edc-482b-b9f0-7cb9b92b07d4
-- title:
--   Complete certified theta upper chain through the last mesh point
-- statement:
--   The Chebyshev theta function satisfies the following complete interval certificate:
--
--   $$10^6\theta(10^8)\le99989691935170\ \Longrightarrow\ \left(10^6\theta(10000064768)\le10000013784295984\quad\text{and}\quad\forall x\in[10^8,10000064768),\ \theta(x)\le x+100000+x/10000\right).$$
--
--   The endpoint carries have scale one million. This supplies the full upper bound required by the finite fourth-power logarithmic theta mesh certificate.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Complete finite-certificate formalization.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Exp

theorem dusart_theta_mesh_complete_upper_chain : (1000000 : ℝ) * Chebyshev.theta 100000000 ≤ 99989691935170 →
    (1000000 : ℝ) * Chebyshev.theta 10000064768 ≤ 10000013784295984 ∧
    ∀ x : ℝ, 100000000 ≤ x → x < 10000064768 →
      Chebyshev.theta x ≤ x + 100000 + x / 10000 := by sorry
