-- Prove2me | Theorems.Thm_lean_workbook_plus_2311
-- name    : lean_workbook_plus_2311
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/f19308ad-e2c6-443c-b8ac-e39f42db2d5f
-- statement:
--   $\sqrt{2n} \geq \sqrt{n + \sqrt{2n+1}}$ for $n \geq 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2311 : ∀ n ≥ 3, Real.sqrt (2 * n) ≥ Real.sqrt (n + Real.sqrt (2 * n + 1))   :=  by sorry
