-- Prove2me | Theorems.Thm_lean_workbook_plus_26825
-- name    : lean_workbook_plus_26825
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/50659078-2980-4191-b623-4c158e7fdd8d
-- statement:
--   Prove that $\frac{t+2}{t(t+4)} \geq \frac{22-5t}{36}$ for all positive $t$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26825 (t : ℝ) (ht : 0 < t) : (t + 2) / (t * (t + 4)) ≥ (22 - 5 * t) / 36   :=  by sorry
