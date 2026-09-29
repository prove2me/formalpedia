-- Prove2me | Theorems.Thm_lean_workbook_plus_66970
-- name    : lean_workbook_plus_66970
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/2f485bbd-adc6-4c3a-b522-5a75c93a4112
-- statement:
--   Prove inequality $ 8\left(a^3 + b^3 + c^3\right) \ge 3(a+b)(b+c)(c+a) $, where $\{a,b,c\}\subset\mathbb R^*_+$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66970 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 8 * (a^3 + b^3 + c^3) ≥ 3 * (a + b) * (b + c) * (c + a)   :=  by sorry
