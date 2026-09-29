-- Prove2me | Theorems.Thm_e_plus_pi_irrational
-- name    : e_plus_pi_irrational
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-31T21:35:53.425063+00:00
-- url     : https://prove2.me/theorems/223a668d-b6c8-44f1-af83-5539f14d12bf
-- statement:
--   e + π and e·π cannot both be rational: At least one of e+π, e·π is irrational (since if both were rational, then e and π would be roots of a quadratic with rational coefficients, contradicting their transcendence). Whether either is irrational individually is unknown. It's known both can't be algebraic.
-- source:
--   https://en.wikipedia.org/wiki/Transcendental_number

import Mathlib

import Mathlib

theorem e_plus_pi_irrational :
    Irrational (Real.exp 1 + Real.pi) ∨ Irrational (Real.exp 1 * Real.pi) := by
  sorry
