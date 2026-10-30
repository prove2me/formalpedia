-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_TentDefect
-- name    : AnalyticCombinatorics_Ch8_Partitions_TentDefect
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:59:56.018712+00:00
-- url     : https://prove2.me/theorems/e0397e4c-ceb5-464a-a32d-fd82474b018a
-- title:
--   Tent Defect
-- statement:
--   The source-linked mathematical setting supplies the finite-kernel, rank, moment, renewal or sequence models used by the exact support contracts in this group. The literal model declarations, where catalogued below, retain their source parameters and assumptions. Definition prose must be refined against the actual complete compiler-derived owner before an upload payload is prepared.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/TentDefect.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# The tent / defect function `Φ_W(d) = max(|d| − W, 0)` (renewal route B primitives)

The fixed-window Tanaka-DEFECT route to the renewal limit uses `Φ_W(d) = max(|d| − W, 0)`: it counts
window crossings robustly to the soft far jumps that break the plain window-occupation local time
(route A is dead — fixed-`b` truncation removes constant mass; see `DOCTRINE-walls.md`).

This file banks the certain primitives:
* `tentW_nonneg`, `tentW_ge` (`Φ_W d ≥ |d| − W`, the PZ-transfer with a `−W` loss),
* `tentW_le_abs`, `tentW_lipschitz`,
* `expected_tentW_ge` (`E[Φ_W(D)] ≥ E|D| − W`), turning the banked `E|D_T| ≥ c√T` into growth of the
  defect potential.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- The tent/defect function `Φ_W(d) = max(|d| − W, 0)`. -/
def tentW (W : ℝ) (d : ℝ) : ℝ := max (|d| - W) 0

end AnalyticCombinatorics.Ch8.Partitions.Erdos


