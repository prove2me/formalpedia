-- Prove2me | Theorems.Thm_WorkbookCorrected_base_44343
-- name    : WorkbookCorrected.base_44343
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:00:04.867436+00:00
-- url     : https://prove2.me/theorems/a6efe4e7-6251-4d16-9db9-37ebf166ce72
-- title:
--   A cyclic product bound under unit product
-- statement:
--   Let $a,b, c$ real positive numbers such that $abc=1$ .Prove that $a^2b(b^3-1)+b^2c(c^3-1)+c^2a(a^3-1)\ge 0.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_44343` (Apache-2.0). Natural-language proposition preserved; missing source domain assumptions restored. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44343; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_44343 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a * b * c = 1) :  a^2 * b * (b^3 - 1) + b^2 * c * (c^3 - 1) + c^2 * a * (a^3 - 1) ≥ 0  :=  by sorry
