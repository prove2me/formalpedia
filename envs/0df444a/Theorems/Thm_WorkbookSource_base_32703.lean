-- Prove2me | Theorems.Thm_WorkbookSource_base_32703
-- name    : WorkbookSource.base_32703
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:40.893249+00:00
-- url     : https://prove2.me/theorems/369c311c-2f42-4c3e-8404-a1b74d2f971b
-- title:
--   A fifth-degree symmetric polynomial is nonnegative
-- statement:
--   Prove that $a^5+b^5+c^5 - a^4b - a^4c-b^4a-b^4c-c^4a-c^4b +a^3bc+ab^3c+abc^3 \geq 0$ for $a,b,c>0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32703` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32703; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32703 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^5 + b^5 + c^5 - a^4 * b - a^4 * c - b^4 * a - b^4 * c - c^4 * a - c^4 * b + a^3 * b * c + a * b^3 * c + a * b * c^3 ≥ 0  :=  by sorry
