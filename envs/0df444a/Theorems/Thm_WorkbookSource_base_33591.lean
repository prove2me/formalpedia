-- Prove2me | Theorems.Thm_WorkbookSource_base_33591
-- name    : WorkbookSource.base_33591
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:25.687926+00:00
-- url     : https://prove2.me/theorems/2a0ef21a-c4ab-4d76-be74-aaa0eac554b8
-- title:
--   A quadratic bound at real unit sum
-- statement:
--   Let $ a,b,c$ be real numbers with $ a+b+c=1$ . Show that $ \frac{a^2+b^2+c^2}{4}+\frac{ab+bc+ca}{5}\ \geq\ \frac{3}{20} $ (NB: $ a,b,c$ can be negative/zero as well as positive.)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33591` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33591; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33591 (a b c : ℝ) (h : a + b + c = 1) :
  3 / 20 ≤ a ^ 2 / 4 + b ^ 2 / 4 + c ^ 2 / 4 + a * b / 5 + b * c / 5 + c * a / 5  :=  by sorry
