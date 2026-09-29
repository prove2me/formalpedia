-- Prove2me | Definitions.Def_Applications_QGame_Recurrence
-- name    : Applications_QGame_Recurrence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:45.948733+00:00
-- url     : https://prove2.me/theorems/65692eac-86ee-488b-acb7-94a5949522c3
-- title:
--   Aether Catalog definitions — Applications_QGame_Recurrence
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.QGame.Recurrence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/QGame/Recurrence.lean by skeleton subtraction
import Mathlib
/-
# QGame probability recurrence

This module defines the probability sequence `P q n` arising from a `q`-game and
records its defining recurrence.

For each fixed parameter `q`, the sequence is defined by

* `P q 0 = 1`
* `P q (n+1) = (1 + ∑ j ∈ Finset.range ((n+1) - q), P q j) / (n+1)`.

The summation range only references strictly smaller indices, so the recursion is
well founded.
-/

namespace QGame

open Finset

/-- The `q`-game probability sequence, valued in `ℚ`.

The summation is taken over `(Finset.range ((n+1) - q)).attach` so that the
membership proof is available for the well-foundedness check; the clean recurrence
`P_succ` recovers the ordinary sum form. -/
def P (q : ℕ) : ℕ → ℚ
  | 0 => 1
  | (n + 1) =>
      (1 + ∑ j ∈ (Finset.range ((n + 1) - q)).attach, P q j.1) / ((n : ℚ) + 1)
decreasing_by
  · have hj := j.2
    simp only [Finset.mem_range] at hj
    omega



end QGame


