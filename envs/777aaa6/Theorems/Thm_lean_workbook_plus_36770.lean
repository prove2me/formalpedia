-- Prove2me | Theorems.Thm_lean_workbook_plus_36770
-- name    : lean_workbook_plus_36770
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/432c58ab-d521-4f5e-b370-276d2fbe2529
-- statement:
--   Prove $ \frac{n(n+1)}{2} + 1 - \frac{1}{n+1} = \frac{n^2+n+2}{2} - \frac{1}{n+1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36770 (n : ℕ) : (n * (n + 1)) / 2 + 1 - 1 / (n + 1) = (n ^ 2 + n + 2) / 2 - 1 / (n + 1)   :=  by sorry
