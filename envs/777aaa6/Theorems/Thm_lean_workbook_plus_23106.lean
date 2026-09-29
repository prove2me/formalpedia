-- Prove2me | Theorems.Thm_lean_workbook_plus_23106
-- name    : lean_workbook_plus_23106
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/0920b6ef-a877-4837-a28a-492b38ff92f1
-- statement:
--   We have a system of two equations: $l = $ Amount Sold Last Week $t = $ Amount Sold This Week From there we get our first equation based on the fact that she sold this week six more than three times last week $l = 3t + 6$ and our second one based on the fact that the amount sold last week and this week totals to $110$ . $l + t = 110$ We transform the second equation like so: $l + t - l = 110 - l$ $t = 110 - l$ From there we plug in the newly transformed second equation into the first to get $l = 3(110 -l) + 6$ This simplifies to $l = 330 - 3l + 6$ or $l = 84$ Then we substitute $l$ into the second equation to get $t = 110 - (84)$ or $t = 26$ Therefore, she sold $84$ CD's on the first week and $26$ on the second.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23106 (l t : ℕ) (h₁ : l = 3 * t + 6) (h₂ : l + t = 110) : l = 84 ∧ t = 26   :=  by sorry
