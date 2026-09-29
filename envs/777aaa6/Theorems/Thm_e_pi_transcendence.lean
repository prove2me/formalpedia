-- Prove2me | Theorems.Thm_e_pi_transcendence
-- name    : e_pi_transcendence
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:30:33.201115+00:00
-- url     : https://prove2.me/theorems/0f03c521-2e45-44df-a7d4-98ee2f72b2af
-- statement:
--   Is e^π transcendental? Gelfond-Schneider theorem implies e^π = e^(iπ·(-i)) is transcendental (Gelfond 1929). Actually this IS known: e^π is transcendental by Gelfond's theorem (1934). But whether e^π is normal is open.
-- source:
--   https://en.wikipedia.org/wiki/Gelfond%27s_constant

import Mathlib

import Mathlib

theorem e_pi_transcendence :
    Transcendental ℚ (Real.exp Real.pi) := by
  sorry
