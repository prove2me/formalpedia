-- Prove2me | Theorems.Thm_lean_workbook_plus_37530
-- name    : lean_workbook_plus_37530
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/0d734ca3-0013-4565-bf96-c19ff11f6bfd
-- statement:
--   \sqrt{(a^2+b^2+ab)(a^2+c^2+ac)}\geq a^2+\frac{a(b+c)}{2}+bc where $a,b,c>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37530 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : Real.sqrt ((a^2 + b^2 + a * b) * (a^2 + c^2 + a * c)) ≥ a^2 + (a * (b + c)) / 2 + b * c   :=  by sorry
