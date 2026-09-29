-- Prove2me | Theorems.Thm_lean_workbook_plus_69849
-- name    : lean_workbook_plus_69849
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/ec9573b6-3545-4645-8f73-1ce5cb48d975
-- statement:
--   Let $z=a+bi$ . The first equation gives us $|a+(b-3)i|=3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69849 (a b : ℝ) (h₁ : ‖a + (b - 3) * Complex.I‖ = 3) : a^2 + (b-3)^2 = 9   :=  by sorry
