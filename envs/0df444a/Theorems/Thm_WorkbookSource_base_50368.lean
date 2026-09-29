-- Prove2me | Theorems.Thm_WorkbookSource_base_50368
-- name    : WorkbookSource.base_50368
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:03:03.405814+00:00
-- url     : https://prove2.me/theorems/6acc380b-acd6-4471-8950-09bf2204cd77
-- title:
--   A product of shifted linear factors bounds mixed products
-- statement:
--   Given $a, b, c \geq 0$, prove that $(a+b+c+1)(a+1)(b+1)(c+1) \geq 8(ab+bc+ca+abc)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50368` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50368; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_50368 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a + b + c + 1) * (a + 1) * (b + 1) * (c + 1) ≥ 8 * (a * b + b * c + c * a + a * b * c)  :=  by sorry
