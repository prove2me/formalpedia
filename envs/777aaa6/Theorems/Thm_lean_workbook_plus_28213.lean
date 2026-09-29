-- Prove2me | Theorems.Thm_lean_workbook_plus_28213
-- name    : lean_workbook_plus_28213
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/fbacd5a5-0e4d-445e-bbaa-1829b04bee7a
-- statement:
--   For \( a, b, c \in \mathbb{R}^{+} \) prove that \[a^3 + b^3 + c^3 \geqslant 3abc\] Should I use \(QM \geqslant AM\geqslant GM \geqslant HM\) ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28213 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 ≥ 3 * a * b * c   :=  by sorry
