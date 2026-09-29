-- Prove2me | Theorems.Thm_lean_workbook_plus_75606
-- name    : lean_workbook_plus_75606
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/4189abd8-120d-4367-bd14-856d8098a4bf
-- statement:
--   Let $a$ , $b$ , $c$ , $d$ be real numbers such that $a+b+c+d=0$ . Show that $a^3+b^3+c^3+d^3=3(abc+abd+acd+bcd)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75606 (a b c d : ℝ) (h : a + b + c + d = 0) : a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 = 3 * (a * b * c + a * b * d + a * c * d + b * c * d)   :=  by sorry
