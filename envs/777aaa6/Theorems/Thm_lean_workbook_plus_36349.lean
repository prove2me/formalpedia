-- Prove2me | Theorems.Thm_lean_workbook_plus_36349
-- name    : lean_workbook_plus_36349
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/e8d43fb8-96fb-446e-8fbc-4404835617d8
-- statement:
--   $RHS=(ab+cd)(bc+da) \le \frac{(ab+bc+cd+da)^{2}}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36349 (a b c d : ℝ) : (a * b + c * d) * (b * c + d * a) ≤ (a * b + b * c + c * d + d * a) ^ 2 / 4   :=  by sorry
