-- Prove2me | Theorems.Thm_lean_workbook_plus_80875
-- name    : lean_workbook_plus_80875
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/11a95bb5-4106-4099-b72a-df027f3d0fde
-- statement:
--   prove the inequality: $\frac{Cos(b)Cos(c)}{Cos(\frac{b-c}{2})}+\frac{Cos(a)Cos(b)}{Cos(\frac{a-b}{2})}+\frac{Cos(a)(Cos(c)}{Cos(\frac{a-c}{2})}\le \frac{3}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80875 : ∀ a b c : ℝ, (cos b * cos c) / cos ((b - c) / 2) + (cos a * cos b) / cos ((a - b) / 2) + (cos a * cos c) / cos ((a - c) / 2) ≤ 3 / 4   :=  by sorry
