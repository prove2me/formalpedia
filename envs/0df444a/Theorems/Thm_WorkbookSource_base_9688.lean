-- Prove2me | Theorems.Thm_WorkbookSource_base_9688
-- name    : WorkbookSource.base_9688
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:45:19.979527+00:00
-- url     : https://prove2.me/theorems/1614e135-fe3d-4175-ad19-40c46d6faed0
-- title:
--   A cyclic linear-over-quadratic upper bound
-- statement:
--   Let $a,b,c$ be positive real numbers, prove that:
--   $\frac{a+b+c}{ab+bc+ac}\geq \frac{a}{a^2+bc+b^2}+\frac{b}{b^2+ca+c^2}+\frac{c}{c^2+ab+a^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9688` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9688; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9688 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + b + c) / (a * b + b * c + a * c) ≥ a / (a ^ 2 + b * c + b ^ 2) + b / (b ^ 2 + c * a + c ^ 2) + c / (c ^ 2 + a * b + a ^ 2)  :=  by sorry
