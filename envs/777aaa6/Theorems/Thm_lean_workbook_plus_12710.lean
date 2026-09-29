-- Prove2me | Theorems.Thm_lean_workbook_plus_12710
-- name    : lean_workbook_plus_12710
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/5e665007-97a1-4e69-8d2a-bcf3a0b869ab
-- statement:
--   Prove that for positive real numbers $a$, $b$, and $c$, the following inequality holds:\n$$(b^{2}-bc+c^{2})(b-c)^{2}+(c^{2}-ca+a^{2})(c-a)^{2}+(a^{2}-ab+b^{2})(a-b)^{2}\geq 0$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12710 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b^2 - b*c + c^2)*(b - c)^2 + (c^2 - c*a + a^2)*(c - a)^2 + (a^2 - a*b + b^2)*(a - b)^2 ≥ 0   :=  by sorry
