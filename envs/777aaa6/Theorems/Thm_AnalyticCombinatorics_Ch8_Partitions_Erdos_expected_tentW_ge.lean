-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_expected_tentW_ge
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.expected_tentW_ge
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:01:53.406377+00:00
-- url     : https://prove2.me/theorems/9f03b2c8-2aa6-4737-b133-708eed94dd3a
-- title:
--   A tent-defect expectation lower bound
-- statement:
--   Elementary Lipschitz/expectation inequalities for max(|d|−W,0); they do not produce nondegenerate variance or a partition coupling.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma expected_tentW_ge (W : ℝ) (D : ι → ℝ) (μ : ι → ℝ)
--       (hμsum : ∑ x, μ x = 1) (hμnn : ∀ x, 0 ≤ μ x) :
--       (∑ x, μ x * |D x|) - W ≤ ∑ x, μ x * tentW W (D x)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/TentDefect.lean#L65. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_TentDefect
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

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.expected_tentW_ge (W : ℝ) (D : ι → ℝ) (μ : ι → ℝ)
    (hμsum : ∑ x, μ x = 1) (hμnn : ∀ x, 0 ≤ μ x) :
    (∑ x, μ x * |D x|) - W ≤ ∑ x, μ x * tentW W (D x) := by sorry
