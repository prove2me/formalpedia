-- Prove2me | Theorems.Thm_lean_workbook_plus_19567
-- name    : lean_workbook_plus_19567
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/63068067-e7d4-4539-b789-dae8f5e07699
-- statement:
--   Prove that if $ n>2$ then $ 3^n > 3n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19567 (n : ℕ) (hn : 2 < n) : 3^n > 3*n   :=  by sorry
