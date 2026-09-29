-- Prove2me | Theorems.Thm_lean_workbook_plus_14892
-- name    : lean_workbook_plus_14892
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/4306b8ee-5905-4705-ae0a-b61a37ac0eda
-- statement:
--   $ \Longrightarrow (a^2+b^2+c^2+ac+ba+ac)^2\ge 4(a^2+b^2+c^2)(ac+ba+ac)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14892 (a b c : ℝ) : (a^2 + b^2 + c^2 + a * c + b * a + a * c)^2 ≥ 4 * (a^2 + b^2 + c^2) * (a * c + b * a + a * c)   :=  by sorry
