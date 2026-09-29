-- Prove2me | Theorems.Thm_lean_workbook_plus_63429
-- name    : lean_workbook_plus_63429
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/4a6431b2-6913-482e-8025-6aba3d4f582b
-- statement:
--   The sum $1^2 + 2^2 + 3^2 + 4^2 + \dots + 25^2$ is equal to $5525$ . Evaluate $2^2 + 4^2 + 6^2 + 8^2 + \dots + 50^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63429 (h₁ : ∑ i in Finset.range 25, (i + 1)^2 = 5525) : ∑ i in Finset.range 25, (2 * (i + 1))^2 = 22100   :=  by sorry
