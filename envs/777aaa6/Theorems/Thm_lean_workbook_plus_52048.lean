-- Prove2me | Theorems.Thm_lean_workbook_plus_52048
-- name    : lean_workbook_plus_52048
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/98fa0c04-7edc-462b-bcf6-c728dba8292d
-- statement:
--   by AM - GM , $x+y = 2 \geq 2\sqrt{xy}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52048 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y = 2) : 2 * Real.sqrt (x * y) ≤ 2   :=  by sorry
