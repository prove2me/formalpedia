-- Prove2me | Theorems.Thm_lean_workbook_plus_20446
-- name    : lean_workbook_plus_20446
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/869c7264-52f9-44fa-94c0-5827e9379310
-- statement:
--   Show that $8(abcd+1) > (1+a)(1+b)(1+c)(1+d)$ for all $a,b,c,d > 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20446 (a b c d : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d) : 8 * (a * b * c * d + 1) > (1 + a) * (1 + b) * (1 + c) * (1 + d)   :=  by sorry
