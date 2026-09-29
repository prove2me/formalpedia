-- Prove2me | Theorems.Thm_WorkbookSource_base_28597
-- name    : WorkbookSource.base_28597
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:02:52.891614+00:00
-- url     : https://prove2.me/theorems/c8558b11-4d57-4515-82f8-a2ac9582a01c
-- title:
--   A symmetric quadratic ratio with a cyclic cubic correction
-- statement:
--   Prove that $\frac{a^2+b^2+c^2}{ab+bc+ca}+\frac{a^2b+b^2c+c^2a}{a^2c+c^2b+b^2a}\ge 2 $ for $a,b,c > 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28597` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28597; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28597 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + c * a) + (a^2 * b + b^2 * c + c^2 * a) / (a^2 * c + c^2 * b + b^2 * a) ≥ 2  :=  by sorry
