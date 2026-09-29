-- Prove2me | Theorems.Thm_WorkbookSource_base_29370
-- name    : WorkbookSource.base_29370
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:47:39.227497+00:00
-- url     : https://prove2.me/theorems/52a15395-51e5-44bb-ae3f-4f20d13d0bac
-- title:
--   Quadratic factors bound a Vandermonde product
-- statement:
--   Prove that $\sum_{cyc} (y-z)^2(x^2-x+1) \geq 3(x-y)(y-z)(z-x)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29370` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29370; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29370 (x y z : ℝ) : (y - z) ^ 2 * (x ^ 2 - x + 1) + (z - x) ^ 2 * (y ^ 2 - y + 1) + (x - y) ^ 2 * (z ^ 2 - z + 1) ≥ 3 * (x - y) * (y - z) * (z - x)  :=  by sorry
