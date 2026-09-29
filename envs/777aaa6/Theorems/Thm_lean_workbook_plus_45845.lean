-- Prove2me | Theorems.Thm_lean_workbook_plus_45845
-- name    : lean_workbook_plus_45845
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/620fa32c-a8ca-4ea0-a596-f09936d6f7aa
-- statement:
--   Let $x = 7$ . Find $\frac{x-1}{x} \cdot \frac{x-2}{x-1} \cdot \frac{x-3}{x-2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45845 (x : ℝ) (hx : x = 7) : (x - 1) / x * (x - 2) / (x - 1) * (x - 3) / (x - 2) = 4 / 7   :=  by sorry
