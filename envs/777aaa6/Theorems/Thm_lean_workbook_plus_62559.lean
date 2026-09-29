-- Prove2me | Theorems.Thm_lean_workbook_plus_62559
-- name    : lean_workbook_plus_62559
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/21d8d83c-1f54-4a21-ba6e-a2c7710d1709
-- statement:
--   Prove that $ (a-1)(b-1)(c-1)<0\Longleftrightarrow abc-ab-bc-ca+a+b+c-1<0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62559 : (a - 1) * (b - 1) * (c - 1) < 0 ↔ a * b * c - a * b - b * c - c * a + a + b + c - 1 < 0   :=  by sorry
