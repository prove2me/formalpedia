-- Prove2me | Theorems.Thm_lean_workbook_plus_34200
-- name    : lean_workbook_plus_34200
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/51a27242-f4fc-4702-a764-ff6990433649
-- statement:
--   Prove that if $5{{x}^{2}}+2y\ge 5{{y}^{2}}+2x$, then $\frac{1}{5(5{{x}^{2}}+2y)+4}\le \frac{1}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34200 : 5 * x ^ 2 + 2 * y ≥ 5 * y ^ 2 + 2 * x → (1 / (5 * (5 * x ^ 2 + 2 * y) + 4)) ≤ 1 / 3   :=  by sorry
