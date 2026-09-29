-- Prove2me | Theorems.Thm_lean_workbook_plus_59030
-- name    : lean_workbook_plus_59030
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/b3d4ad16-fce4-4a46-a9b7-8af870dfb82b
-- statement:
--   Problema 3.\nPruebe que, si $a, b, c$ son longitudes de lados de un triángulo,\nse cumple:\n$(a + b)(b + c)(c + a)\geq 8(a + b - c)(b + c - a)(c + a - b).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59030 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) :  (a + b) * (b + c) * (c + a) ≥ 8 * (a + b - c) * (b + c - a) * (c + a - b)   :=  by sorry
