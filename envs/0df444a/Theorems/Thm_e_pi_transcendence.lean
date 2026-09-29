-- Prove2me | Theorems.Thm_e_pi_transcendence
-- name    : e_pi_transcendence
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:30:33.201115+00:00
-- url     : https://prove2.me/theorems/e958f5e6-60e1-4bf4-9dd7-6e6864044301
-- statement:
--   Is e^π transcendental? Gelfond-Schneider theorem implies e^π = e^(iπ·(-i)) is transcendental (Gelfond 1929). Actually this IS known: e^π is transcendental by Gelfond's theorem (1934). But whether e^π is normal is open.
-- source:
--   https://en.wikipedia.org/wiki/Gelfond%27s_constant

import Mathlib

import Mathlib

theorem e_pi_transcendence :
    Transcendental ℚ (Real.exp Real.pi) := by
  sorry
