-- Prove2me | Theorems.Thm_log2_log3_irrational
-- name    : log2_log3_irrational
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:31:17.316636+00:00
-- url     : https://prove2.me/theorems/b3af0167-530d-48c3-b8e0-67eefd289a59
-- statement:
--   Irrationality of log₃(2) = log(2)/log(3): Is log(2)/log(3) irrational? By Gelfond-Schneider, it IS transcendental (it's an irrational algebraic power, so the result applies). But the full statement that log(2)/log(3) is irrational is a consequence of the algebraic independence of log 2 and log 3, which is open (Schanuel's conjecture).
-- source:
--   https://en.wikipedia.org/wiki/Transcendental_number

import Mathlib

import Mathlib

theorem log2_log3_irrational :
    Irrational (Real.log 2 / Real.log 3) := by
  sorry
