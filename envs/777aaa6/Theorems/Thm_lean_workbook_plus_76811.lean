-- Prove2me | Theorems.Thm_lean_workbook_plus_76811
-- name    : lean_workbook_plus_76811
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/700374cf-5457-4e35-ac76-46cca3799df0
-- statement:
--   Thus, the solution set is $ k=13n+4$ for $ n\in\mathbb{Z}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76811 (k : ℤ) : (∃ n : ℤ, k = 13*n + 4) ↔ (k ≡ 4 [ZMOD 13])   :=  by sorry
