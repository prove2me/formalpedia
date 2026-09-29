-- Prove2me | Theorems.Thm_lean_workbook_plus_54986
-- name    : lean_workbook_plus_54986
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/018246f9-67f1-49f7-98f5-41b47a32f99f
-- statement:
--   Given $a=b=c=d=e=\frac{1}{5}$, prove that $abcde+4 \ge abcd+abce+abde+acde+bcde$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54986 (a b c d e : ℝ) (ha : a = 1 / 5) (hb : b = 1 / 5) (hc : c = 1 / 5) (hd : d = 1 / 5) (he : e = 1 / 5) : a * b * c * d * e + 4 ≥ a * b * c * d + a * b * c * e + a * b * d * e + a * c * d * e + b * c * d * e   :=  by sorry
