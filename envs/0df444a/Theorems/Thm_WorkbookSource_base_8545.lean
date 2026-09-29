-- Prove2me | Theorems.Thm_WorkbookSource_base_8545
-- name    : WorkbookSource.base_8545
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:11:07.056996+00:00
-- url     : https://prove2.me/theorems/91ac02da-3e59-47f5-88d8-f92fc5d7940c
-- title:
--   A symmetric fifth-degree inequality with a mixed correction
-- statement:
--   Prove that
--    $a^5+b^5+c^5+abc(ab+bc+ca)\geq a^3(b^2+c^2)+b^3(c^2+a^2)+c^3(a^2+b^2)$
--   where $a, b, c$ are positive.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8545` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8545; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8545 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^5 + b^5 + c^5 + a * b * c * (a * b + b * c + c * a) ≥ a^3 * (b^2 + c^2) + b^3 * (c^2 + a^2) + c^3 * (a^2 + b^2)  :=  by sorry
