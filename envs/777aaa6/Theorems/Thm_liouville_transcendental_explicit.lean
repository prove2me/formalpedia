-- Prove2me | Theorems.Thm_liouville_transcendental_explicit
-- name    : liouville_transcendental_explicit
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:41:34.754696+00:00
-- url     : https://prove2.me/theorems/086b449c-c09d-4ce0-ae23-f6074fb9a3a4
-- statement:
--   Liouville's constant: ∑ 10^{-n!} is transcendental (first proved transcendental number, Liouville 1851). More generally, any Liouville number is transcendental.
-- source:
--   https://en.wikipedia.org/wiki/Liouville_number

import Mathlib

import Mathlib

theorem liouville_transcendental_explicit :
    Transcendental ℚ (∑' n : ℕ, (1 : ℝ) / 10 ^ (n.factorial)) := by
  sorry
