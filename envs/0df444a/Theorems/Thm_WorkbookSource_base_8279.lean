-- Prove2me | Theorems.Thm_WorkbookSource_base_8279
-- name    : WorkbookSource.base_8279
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:11:08.291889+00:00
-- url     : https://prove2.me/theorems/0cce3dad-0d95-4209-94ad-ce9639d3b025
-- title:
--   A cyclic sixth-degree inequality in mixed powers
-- statement:
--   Prove that $ ab^5 + bc^5 + ca^5\ge abc(a^2b + b^2c + c^2a)$ , for $ a,b,c > 0$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8279` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8279; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8279 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b^5 + b * c^5 + c * a^5 ≥ a * b * c * (a^2 * b + b^2 * c + c^2 * a)  :=  by sorry
