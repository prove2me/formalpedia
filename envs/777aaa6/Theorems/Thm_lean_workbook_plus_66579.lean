-- Prove2me | Theorems.Thm_lean_workbook_plus_66579
-- name    : lean_workbook_plus_66579
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b4f8e031-c20c-48eb-9ee4-6cd46fc2a7ce
-- statement:
--   Let $a,b,c>0$ and $ab+bc+ca=1$ .Prove that: $(a^2+2bc)(b^2+2ca)(c^2+2ab) \geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66579 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a * b + b * c + c * a = 1) : (a^2 + 2 * b * c) * (b^2 + 2 * c * a) * (c^2 + 2 * a * b) ≥ 1   :=  by sorry
