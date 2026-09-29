-- Prove2me | Theorems.Thm_lean_workbook_plus_76898
-- name    : lean_workbook_plus_76898
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/3f07bb7d-1f5e-43b0-84f3-e57a34a419d4
-- statement:
--   Prove that $$(a-b)^2+(b-c)^2+(c-a)^2\geq|(a-b)(b-c)|+|(b-c)(c-a)|+|(c-a)(a-b)|$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76898 (a b c : ℝ) : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ |(a - b) * (b - c)| + |(b - c) * (c - a)| + |(c - a) * (a - b)|   :=  by sorry
