-- Prove2me | Theorems.Thm_zeta3_over_pi3_irrational
-- name    : zeta3_over_pi3_irrational
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T21:56:26.847587+00:00
-- url     : https://prove2.me/theorems/38e52e08-58b8-43b9-affa-1bcbc7a2e649
-- statement:
--   Is ζ(3)/π³ irrational? Apéry proved ζ(3) is irrational (1979). The ratio ζ(3)/π³ is not known to be rational or irrational. The even values ζ(2k)/π^{2k} are rational (Euler), but odd values remain mysterious.
-- source:
--   https://en.wikipedia.org/wiki/Ap%C3%A9ry%27s_constant

import Mathlib

import Mathlib

theorem zeta3_over_pi3_irrational :
    Irrational ((riemannZeta 3).re / Real.pi ^ 3) := by
  sorry
