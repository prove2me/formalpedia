-- Prove2me | Theorems.Thm_lean_workbook_plus_9975
-- name    : lean_workbook_plus_9975
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/5370d317-1d16-4235-89f4-8855f6d3efaa
-- statement:
--   Prove that $n^n>(n+1)^{n-1}$ for all positive integers $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9975 : ∀ n : ℕ, n^n > (n + 1)^(n - 1)   :=  by sorry
