-- Prove2me | Theorems.Thm_lean_workbook_plus_80927
-- name    : lean_workbook_plus_80927
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/5686f70a-22f6-4451-9c9e-23502ffeb003
-- statement:
--   Let $a, b, c \ge 0$ . Prove that $(a+b)(b+c)(c+a) \ge 8abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80927 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a + b) * (b + c) * (c + a) ≥ 8 * a * b * c   :=  by sorry
