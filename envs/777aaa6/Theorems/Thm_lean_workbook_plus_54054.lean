-- Prove2me | Theorems.Thm_lean_workbook_plus_54054
-- name    : lean_workbook_plus_54054
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/d8215c81-5141-4298-b9a3-b13e126d371b
-- statement:
--   Prove $(a+b+c)^2\ge 3(ab+bc+ca)$ for $a=xy;b=yz;c=zx$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54054 (a b c : ℝ) (ha : a = xy) (hb : b = yz) (hc : c = zx) : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a)   :=  by sorry
