-- Prove2me | Theorems.Thm_lean_workbook_plus_51008
-- name    : lean_workbook_plus_51008
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/017b413d-e43a-45ef-acf8-2356db4fdccb
-- statement:
--   $(a-2)(b-2)+(b-2)(c-2)+(c-2)(a-2)\geq 0\ \ \iff \ \ ab+bc+ca+4(3-a-b-c)\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51008 :  (a - 2) * (b - 2) + (b - 2) * (c - 2) + (c - 2) * (a - 2) ≥ 0 ↔    a * b + b * c + c * a + 4 * (3 - a - b - c) ≥ 0   :=  by sorry
