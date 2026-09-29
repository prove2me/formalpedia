-- Prove2me | Theorems.Thm_lean_workbook_plus_75759
-- name    : lean_workbook_plus_75759
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/ebfb88e8-f6b1-4d74-ab21-f73963784efe
-- statement:
--   Prove that $(n+1) \le \left(\frac{n+1}{n}\right)^n \cdot (n+2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75759 (n : ℕ) (hn : 0 < n) : (n + 1) ≤ ((n + 1) / n)^n * (n + 2)   :=  by sorry
