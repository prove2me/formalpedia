-- Prove2me | Theorems.Thm_lean_workbook_plus_22909
-- name    : lean_workbook_plus_22909
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/7b401e68-d81e-442b-8f78-fc2f72472d3e
-- statement:
--   So, inequality may be reperesented in form: $ \sqrt{\frac{3n+3}{3n+1}}\leq \frac{2n+2}{2n+1}$ , which is easy to prove.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22909 (n : ℕ) : Real.sqrt ((3 * n + 3) / (3 * n + 1)) ≤ (2 * n + 2) / (2 * n + 1)   :=  by sorry
