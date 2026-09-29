-- Prove2me | Theorems.Thm_lean_workbook_plus_30624
-- name    : lean_workbook_plus_30624
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/65e346e3-4be2-4762-82b9-5b02e4fda5f9
-- statement:
--   Let $a,b,c\geq 0,a+b+c=1$ ,prove that: $(a+b)(b+c)(c+a) \ge \frac89(a+b+c)(ab+bc+ca)=\frac89(ab+bc+ca)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30624 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c = 1) :  (a + b) * (b + c) * (c + a) ≥ 8 / 9 * (a + b + c) * (a * b + b * c + c * a)   :=  by sorry
