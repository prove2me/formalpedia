-- Prove2me | Theorems.Thm_lean_workbook_plus_12140
-- name    : lean_workbook_plus_12140
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/8f459f05-2f93-4df6-96d7-0546a47114ba
-- statement:
--   If $a,b,c,d$ are positive real numbers then prove that $(1+a^4)(1+b^4)(1+c^4)(1+d^4)\ge (1+(abcd)^4)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12140 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (1 + a^4) * (1 + b^4) * (1 + c^4) * (1 + d^4) ≥ 1 + (a * b * c * d)^4   :=  by sorry
