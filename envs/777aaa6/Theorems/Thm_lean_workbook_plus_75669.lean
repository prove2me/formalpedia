-- Prove2me | Theorems.Thm_lean_workbook_plus_75669
-- name    : lean_workbook_plus_75669
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/3926b905-cb07-4a45-b965-f812ecb6ebdf
-- statement:
--   Let $n$ be a positive integer, prove that\n $ \sqrt{n+1} - \sqrt{n} < \frac{1}{2 \sqrt n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75669 (n : ℕ) (hn : 0 < n) : (Real.sqrt (n + 1) - Real.sqrt n) < 1 / (2 * Real.sqrt n)   :=  by sorry
