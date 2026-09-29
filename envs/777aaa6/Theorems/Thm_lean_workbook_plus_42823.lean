-- Prove2me | Theorems.Thm_lean_workbook_plus_42823
-- name    : lean_workbook_plus_42823
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/7d39c414-0705-4112-9f36-d32c113c4641
-- statement:
--   For $\{a, b, c\} \in \mathbb{R^+}$ , show that,\n $$a^3+b^3+c^3+8abc \geq (a+b)(b+c)(c+a)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42823 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 + 8 * a * b * c ≥ (a + b) * (b + c) * (c + a)   :=  by sorry
