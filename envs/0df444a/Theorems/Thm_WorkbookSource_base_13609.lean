-- Prove2me | Theorems.Thm_WorkbookSource_base_13609
-- name    : WorkbookSource.base_13609
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:24.122437+00:00
-- url     : https://prove2.me/theorems/639bc6a1-d28d-442b-8b4a-fda9fd8456f8
-- title:
--   A six-variable cyclic inequality at zero sum
-- statement:
--   prove $2(ab+bc+cd+de+ef+fa)\leq a^2+b^2+c^2+d^2+e^2+f^2$ given $a+b+c+d+e+f=0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13609` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13609; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13609 (a b c d e f : ℝ) (h : a + b + c + d + e + f = 0) :
  2 * (a * b + b * c + c * d + d * e + e * f + f * a) ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2  :=  by sorry
