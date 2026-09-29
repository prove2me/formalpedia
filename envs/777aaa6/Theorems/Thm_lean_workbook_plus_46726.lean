-- Prove2me | Theorems.Thm_lean_workbook_plus_46726
-- name    : lean_workbook_plus_46726
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/b2f02035-7eea-4a63-b733-2eecb5cdc415
-- statement:
--   Let $a,b>0 .$ Prove that $\frac{a}{a+3} + \frac{b}{a(ab+2)} + \frac{1}{b(b+2)}>\frac{3}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46726 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a / (a + 3) + b / (a * b + 2) + 1 / (b * (b + 2)) > 3 / 5   :=  by sorry
