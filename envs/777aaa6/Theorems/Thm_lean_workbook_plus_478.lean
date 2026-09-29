-- Prove2me | Theorems.Thm_lean_workbook_plus_478
-- name    : lean_workbook_plus_478
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/6bc3c2ea-2f85-42eb-873b-cf1c1aa9fd13
-- statement:
--   Let $a,b,c,d$ be non-negative real numbers such that $a^{3}+b^{3}+c^{3}+d^3 \le d^2$. Show that $a^4+b^4+c^4+d^4\ge{d^5}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_478 {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (habc : a * b * c = 1) (h : a^3 + b^3 + c^3 + d^3 ≤ d^2) : a^4 + b^4 + c^4 + d^4 ≥ d^5   :=  by sorry
