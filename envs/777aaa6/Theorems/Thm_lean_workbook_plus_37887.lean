-- Prove2me | Theorems.Thm_lean_workbook_plus_37887
-- name    : lean_workbook_plus_37887
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/5f7f7b40-e649-42c4-8722-163ed1834903
-- statement:
--   Prove $a^3+b^3 = (a+b)(a^2-ab+b^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37887 (a b : ℤ) : a^3 + b^3 = (a + b) * (a^2 - a * b + b^2)   :=  by sorry
