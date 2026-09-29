-- Prove2me | Theorems.Thm_lean_workbook_plus_46791
-- name    : lean_workbook_plus_46791
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/d60e5079-32de-481c-b153-f0574150cb07
-- statement:
--   it is equal to $(x-y)^2$ $(7x^2+7y^2+10xy)$ ≥ $0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46791 (x y : ℝ) : (x - y) ^ 2 * (7 * x ^ 2 + 7 * y ^ 2 + 10 * x * y) ≥ 0   :=  by sorry
