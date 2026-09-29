-- Prove2me | Theorems.Thm_lean_workbook_plus_13020
-- name    : lean_workbook_plus_13020
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/73d35fd2-5bd1-4699-8377-32b665071015
-- statement:
--   The total is then $3\sum_{k=1}^9k^2=3\cdot\frac{9\cdot10\cdot19}6=\boxed{855}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13020 3 * ∑ k in Finset.range 10, k^2 = 855   :=  by sorry
