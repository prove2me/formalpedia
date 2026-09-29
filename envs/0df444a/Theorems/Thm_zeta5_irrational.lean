-- Prove2me | Theorems.Thm_zeta5_irrational
-- name    : zeta5_irrational
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:30:55.029575+00:00
-- url     : https://prove2.me/theorems/9c6d8d5d-393a-4be3-9ba6-112bcc51f0e3
-- statement:
--   Irrationality of ζ(5): Is ζ(5) = 1 + 1/32 + 1/243 + ... irrational? Apéry proved ζ(3) is irrational (1979). Ball-Rivoal (2000) proved infinitely many odd values ζ(2k+1) are irrational; but ζ(5) specifically remains unproved to be irrational.
-- source:
--   https://en.wikipedia.org/wiki/Ap%C3%A9ry%27s_constant

import Mathlib

import Mathlib

theorem zeta5_irrational :
    Irrational (riemannZeta 5).re := by
  sorry
