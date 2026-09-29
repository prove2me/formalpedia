-- Prove2me | Theorems.Thm_lean_workbook_plus_50353
-- name    : lean_workbook_plus_50353
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/793ccd90-5fa0-4eb9-8594-cd130f130985
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a^2+b^2+c^2+2abc=1$ . Prove: $a+b+c \le \dfrac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50353 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 1) : a + b + c ≤ 3 / 2   :=  by sorry
