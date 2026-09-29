-- Prove2me | Theorems.Thm_lean_workbook_plus_49159
-- name    : lean_workbook_plus_49159
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/40ae5ae3-a181-41f6-8a12-4e7617100fdb
-- statement:
--   $ 10 + 24 > x \implies x < 34\\10 + x > 24 \implies x > 14$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49159 (x : ℝ) : 10 + 24 > x → x < 34 ∧ 10 + x > 24 → x > 14   :=  by sorry
