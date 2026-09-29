-- Prove2me | Theorems.Thm_riemannZeta_neg_odd_ne_zero
-- name    : riemannZeta_neg_odd_ne_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T22:18:45.087902+00:00
-- url     : https://prove2.me/theorems/a58935ac-4622-43dd-9a44-324643799c43
-- title:
--   Riemann zeta is nonzero at negative odd integers
-- statement:
--   For every odd natural number $n$, the Riemann zeta value at the negative odd integer $-n$ is nonzero. Together with the trivial-zero formula at negative even integers, this separates the integral zeros of zeta by parity.
-- source:
--   Classical special values $\zeta(-n)=(-1)^n B_{n+1}/(n+1)$ and Euler’s nonvanishing formula for even Bernoulli numbers; see Mathlib’s Riemann zeta special-value theorems.

import Mathlib

open Complex

theorem riemannZeta_neg_odd_ne_zero (n : ℕ) (hn : Odd n) :
    riemannZeta (-(n : ℂ)) ≠ 0 := by sorry
