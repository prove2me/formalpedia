-- Prove2me | Theorems.Thm_lean_workbook_plus_75
-- name    : lean_workbook_plus_75
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/7af3aefb-7016-41ce-ad35-c76fe85031a6
-- statement:
--   It's equivalent to \n\n $ab+bc+ca\le 3abc+2(a^3+b^3+c^3)$ \n\n $\Leftrightarrow 2(a^3+b^3+c^3)+3abc\ge (ab+bc+ca)(a+b+c)=\sum ab(a+b)+3abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : 2 * (a ^ 3 + b ^ 3 + c ^ 3) + 3 * a * b * c ≥ (a * b + b * c + c * a) * (a + b + c)   :=  by sorry
