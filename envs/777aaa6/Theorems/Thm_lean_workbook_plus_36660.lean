-- Prove2me | Theorems.Thm_lean_workbook_plus_36660
-- name    : lean_workbook_plus_36660
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/af3a46b6-4341-4620-b640-74b2aa8978e4
-- statement:
--   Let $a, b, c>0$ and $\frac{1}{a^2(b+c)} + \frac{1}{b^2(a+c)} + \frac{1}{c^2(a+b)}=1$ . Prove that $$abc \ge \frac{3}{2}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36660 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (1 / (a^2 * (b + c)) + 1 / (b^2 * (a + c)) + 1 / (c^2 * (a + b))) = 1) : a * b * c ≥ 3 / 2   :=  by sorry
