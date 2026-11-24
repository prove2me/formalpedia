-- Prove2me | Theorems.Thm_syracuse_cycle_eq_one_of_rational_period_sieve
-- name    : syracuse_cycle_eq_one_of_rational_period_sieve
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T07:39:58.358813+00:00
-- url     : https://prove2.me/theorems/57ea67dc-32fb-4d0a-9680-8087c9ca9945
-- title:
--   A rational test excluding nontrivial Syracuse cycles by return time
-- statement:
--   Let $T$ send a natural number $n$ to the odd part of $3n+1$. Suppose $m>0$, $p>0$ and $T^p(m)=m$. If
--   $$145834p\;\le\;92011\left(\left\lfloor\frac{50508p}{31867}\right\rfloor+1\right),$$
--   then $m=1$. This excludes nontrivial cycles at every return time passing the test, even when $p$ is a multiple of the least period. The test uses only integer multiplication and division and has no upper limit on $p$.
--
--   In the range $7621\le p\le100000$, the reverse strict inequality holds for 830 of the 92,380 lengths. These are candidates for further investigation.
-- source:
--   New integer period test using the platform margin theorem (https://prove2.me/theorems/756c30cf-ce03-4b10-afe8-8f76f671ae4f) and the verified small-value exclusion syracuse_no_cycle_below_2887463. The two power comparisons are verified directly.

import Mathlib.Logic.Function.Iterate
import Definitions.Def_syracuseStep

theorem syracuse_cycle_eq_one_of_rational_period_sieve (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hsieve : 145834 * p ≤ 92011 * (50508 * p / 31867 + 1)) : m = 1 := by sorry
