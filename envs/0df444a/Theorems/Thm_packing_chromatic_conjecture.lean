-- Prove2me | Theorems.Thm_packing_chromatic_conjecture
-- name    : packing_chromatic_conjecture
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:45:28.473126+00:00
-- url     : https://prove2.me/theorems/8f95ff0e-2d50-4440-942d-9ac9fa891969
-- statement:
--   Packing chromatic number of the infinite grid: The ℤ² grid has a well-defined packing chromatic number χₚ (minimum colors for infinite packing coloring). Conjectured: χₚ(ℤ²) = 15. Currently known: 13 ≤ χₚ ≤ 15. Open.
-- source:
--   https://en.wikipedia.org/wiki/Packing_coloring

import Mathlib

import Mathlib

theorem packing_chromatic_conjecture :
    ∃ (chi_p : ℕ),
      chi_p ≤ 15 ∧
      ∀ (col : ℤ × ℤ → ℕ) (_ : ∀ p q : ℤ × ℤ,
          col p = col q → p ≠ q →
          chi_p < (p.1 - q.1).natAbs + (p.2 - q.2).natAbs),
        ∃ x : ℤ × ℤ, col x > chi_p := by
  sorry
