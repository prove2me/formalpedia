-- Prove2me | Theorems.Thm_WorkbookSource_base_43488
-- name    : WorkbookSource.base_43488
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:33.48858+00:00
-- url     : https://prove2.me/theorems/721b3b22-b5e8-47e2-a056-07639778870f
-- title:
--   A product inequality involving the elementary symmetric sums
-- statement:
--   Prove that $(a^2+1)(b^2+1)(c^2+1)+8abc\ge (a+b+c+abc)(1+ab+bc+ca)$ for all real $a, b, c$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43488` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43488; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_43488 (a b c : ℝ) : (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) + 8 * a * b * c ≥ (a + b + c + a * b * c) * (1 + a * b + b * c + c * a)  :=  by sorry
