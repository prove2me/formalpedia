-- Prove2me | Theorems.Thm_gowers_polynomial_pattern
-- name    : gowers_polynomial_pattern
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T01:46:14.18555+00:00
-- url     : https://prove2.me/theorems/cfe22ce1-f161-4460-b6d4-7b2cd963fd87
-- statement:
--   Szemerédi's theorem: Every subset of the integers with positive upper density contains arithmetic progressions of arbitrary length. Proved by Szemerédi (1975) and quantitatively by Gowers (2001) using uniformity norms.
-- source:
--   https://en.wikipedia.org/wiki/Szemer%C3%A9di%27s_theorem

import Mathlib

import Mathlib

theorem gowers_polynomial_pattern (k : ℕ) (hk : 2 ≤ k) :
    ∀ (delta : ℝ) (_ : 0 < delta),
    ∃ N : ℕ, ∀ (n : ℕ) (_ : N ≤ n) (A : Finset (Fin n)),
      delta * n ≤ A.card →
      ∃ (a d : ℕ) (_ : 1 ≤ d) (_ : a + k * d < n),
        ∀ j : Fin (k + 1),
          ∃ hlt : a + j.val * d < n, ⟨a + j.val * d, hlt⟩ ∈ A := by
  sorry
