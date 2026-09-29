-- Prove2me | Theorems.Thm_lean_workbook_plus_32581
-- name    : lean_workbook_plus_32581
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/5a333f9b-b8c2-40ff-b3a0-7bb6f8293879
-- statement:
--   $$ \left( \frac{\sqrt{2n+1} - \sqrt{2n-1}}{2} \right)^2 = \frac{4n - 2\sqrt{(2n-1)(2n+1)}}{4} $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32581  ∀ n : ℕ, ((Real.sqrt (2 * n + 1) - Real.sqrt (2 * n - 1)) / 2)^2 = (4 * n - 2 * Real.sqrt ((2 * n - 1) * (2 * n + 1))) / 4   :=  by sorry
