-- Prove2me | Theorems.Thm_davenport_constant_groups
-- name    : davenport_constant_groups
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:40:10.615502+00:00
-- url     : https://prove2.me/theorems/890f8965-008d-46a4-8e96-ce9465c1631e
-- statement:
--   Davenport constant: For cyclic groups ℤₙ, the Davenport constant D(ℤₙ) = 2n-1 (every sequence of 2n-1 elements has a nonempty zero-sum subsequence). For general finite groups, D(G) is determined by the structure of G. Open for some group families.
-- source:
--   https://en.wikipedia.org/wiki/Davenport_constant

import Mathlib

import Mathlib

theorem davenport_constant_groups (n : ℕ) (hn : 1 ≤ n) :
    ∃ (D : ℕ), D = 2 * n - 1 ∧
    ∀ (seq : Fin D → ZMod n),
      ∃ (I : Finset (Fin D)) (_ : I.Nonempty),
        (I.sum seq) = 0 := by
  sorry
