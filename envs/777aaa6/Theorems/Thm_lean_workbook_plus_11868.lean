-- Prove2me | Theorems.Thm_lean_workbook_plus_11868
-- name    : lean_workbook_plus_11868
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/adb8960f-4ec5-43ce-9fc4-89cb79d900b3
-- statement:
--   Let $t$ be the parameter, the curve starts at $t=0,\ x=2$. Hence, let $x=t+2$ , then $y=2(t+2)^2-2(t+2)-4=2t^2+6t$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11868 ∀ t, (t+2, 2*(t+2)^2-2*(t+2)-4) = (t+2, 2*t^2+6*t)   :=  by sorry
