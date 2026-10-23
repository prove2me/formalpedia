-- Prove2me | Theorems.Thm_zeta_ne_zero_of_strip_of_fourteen_lt_im_of_im_le_hundred
-- name    : zeta_ne_zero_of_strip_of_fourteen_lt_im_of_im_le_hundred
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-22T09:51:57.693035+00:00
-- url     : https://prove2.me/theorems/b232bf75-d96c-4fbe-953a-e6068e6a8515
-- title:
--   No zeros of $\zeta$ with $\tfrac12<\operatorname{Re} s<1$ and $14<\operatorname{Im} s\le 100$
-- statement:
--   Let $\zeta$ denote the Riemann zeta function. The Riemann zeta function has no zero strictly to the right of the critical line in the critical strip at heights between $14$ and $100$:
--
--   $$\tfrac12<\operatorname{Re} s<1,\quad 14<\operatorname{Im} s\le 100 \ \Longrightarrow\ \zeta(s)\neq 0.$$
--
--   This is the part of the classical numerical verification of the Riemann hypothesis covering the first $29$ nontrivial zeros (ordinates $14.13\ldots$ up to $98.83\ldots$), which all lie on the critical line. Together with the open statement `zeta_ne_zero_of_strip_of_hundred_lt_im` it yields `zeta_ne_zero_of_strip_of_fourteen_lt_im`; the strict inequality $\tfrac12<\operatorname{Re}s$ is essential, since $\zeta$ does vanish on the critical line in this range.
--
--   It is a direct consequence of the location theorem `TaoFivePrimes.rh_verified_block_14_1e2` (env `0df444a`, proved by @raresbuhai from @sometik179's certificate): every zero with $0<\operatorname{Re}s<1$, $14\le\operatorname{Im}s\le100$ has $\operatorname{Re}s=\tfrac12$.
--
--   **Formalization Note.** `riemannZeta` is Mathlib's analytically continued zeta function; `s.re`, `s.im` are the real and imaginary parts of `s`.
-- source:
--   Numerical verification of RH up to height 100: e.g. A. M. Odlyzko, tables of zeros of the Riemann zeta function (https://www-users.cse.umn.edu/~odlyzko/zeta_tables/), and T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656, Theorem 1.5 (RH verified to height 3.29e9). Formal certificate: Prove2Me theorem TaoFivePrimes.rh_verified_block_14_1e2 (4a25d5fd-e124-4e2c-8ca1-9d998179d1c2, env 0df444a).

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex

theorem zeta_ne_zero_of_strip_of_fourteen_lt_im_of_im_le_hundred (s : ℂ) (h0 : 1 / 2 < s.re)
    (h1 : s.re < 1) (him : 14 < s.im) (him' : s.im ≤ 100) : riemannZeta s ≠ 0 := by sorry
