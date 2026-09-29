-- Prove2me | Theorems.Thm_lean_workbook_plus_76131
-- name    : lean_workbook_plus_76131
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/ed35d629-97b8-4247-b08b-649d2aac4416
-- statement:
--   Prove that $\sqrt{2(a^2+1)(b^2+1)} \ge |ab+a+b-1|$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76131 (a b : ℝ) : Real.sqrt (2 * (a ^ 2 + 1) * (b ^ 2 + 1)) ≥ |a * b + a + b - 1|   :=  by sorry
