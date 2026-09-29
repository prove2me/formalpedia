-- Prove2me | Theorems.Thm_lean_workbook_plus_34099
-- name    : lean_workbook_plus_34099
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/fde52567-9f5e-496c-981c-7f59a8f20354
-- statement:
--   Prove inequality $ 8(a^3 + b^3 + c^3 ) \ge 3(a+b)(b+c)(c+a) $, where $a,b,c \ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34099 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : 8 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ 3 * (a + b) * (b + c) * (c + a)   :=  by sorry
