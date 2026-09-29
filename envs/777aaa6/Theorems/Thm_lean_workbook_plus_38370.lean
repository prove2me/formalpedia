-- Prove2me | Theorems.Thm_lean_workbook_plus_38370
-- name    : lean_workbook_plus_38370
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/74d4c573-0e19-4183-8cab-36459af77047
-- statement:
--   Explain the steps in the solution: $ \binom{n}{2}-n = \frac{n(n-1)}{2}-n = \frac{n(n-3)}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38370 (n : ℕ) : (n.choose 2) - n = n * (n - 3) / 2   :=  by sorry
