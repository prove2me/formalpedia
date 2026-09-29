-- Prove2me | Theorems.Thm_liouville_transcendental_explicit
-- name    : liouville_transcendental_explicit
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:41:34.754696+00:00
-- url     : https://prove2.me/theorems/e4eb2b4a-0c68-4844-ac7d-21fd836cf30e
-- statement:
--   Liouville's constant: ∑ 10^{-n!} is transcendental (first proved transcendental number, Liouville 1851). More generally, any Liouville number is transcendental.
-- source:
--   https://en.wikipedia.org/wiki/Liouville_number

import Mathlib

import Mathlib

theorem liouville_transcendental_explicit :
    Transcendental ℚ (∑' n : ℕ, (1 : ℝ) / 10 ^ (n.factorial)) := by
  sorry
