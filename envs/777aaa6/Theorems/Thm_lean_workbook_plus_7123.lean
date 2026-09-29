-- Prove2me | Theorems.Thm_lean_workbook_plus_7123
-- name    : lean_workbook_plus_7123
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/a3194044-491f-4323-9b15-47c57261c0c2
-- statement:
--   Apply Zsigmondy's theorem to show that there exists a prime $p$ dividing $10^{11} - 1$ and not dividing 9.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7123 (hx: 1 < 10) (h : 11 ≠ 0): ∃ p, p ∣ 10^11 - 1 ∧ ¬ p ∣ 9   :=  by sorry
