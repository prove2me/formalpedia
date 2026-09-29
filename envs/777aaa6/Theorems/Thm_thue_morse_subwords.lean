-- Prove2me | Theorems.Thm_thue_morse_subwords
-- name    : thue_morse_subwords
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:58:37.239594+00:00
-- url     : https://prove2.me/theorems/96d75fb6-20fd-43aa-a386-32a9a1a3b891
-- statement:
--   Thue-Morse sequence: Every finite binary word eventually appears as a subword. The morphism t → 01, 1 → 10 generates an overlap-free infinite word. Complexity questions remain open.
-- source:
--   https://en.wikipedia.org/wiki/Thue%E2%80%93Morse_sequence

import Mathlib

import Mathlib

def thueMorseSeq : ℕ → Bool
    | 0 => false
    | n + 1 => !(thueMorseSeq n)

theorem thue_morse_subwords :
    ∀ w : List Bool, 0 < w.length →
      ∃ n : ℕ,
        w = (List.map thueMorseSeq (List.range n)).take w.length ∨
        w = (List.map thueMorseSeq (List.range (n + w.length))).drop n := by
  sorry
