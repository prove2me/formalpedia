-- Prove2me | Theorems.Thm_lean_workbook_plus_4979
-- name    : lean_workbook_plus_4979
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/7d4064cb-387d-46c3-afa0-34bedc3a3f80
-- statement:
--   Let $ r$ be Rudolph's rate (mph). Since $ 50=r\cdot t$ , the time that it takes him to bike 50 miles is $ \frac{50}{r}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4979 (r t : ℝ) (h₁ : r * t = 50) : t = 50 / r   :=  by sorry
