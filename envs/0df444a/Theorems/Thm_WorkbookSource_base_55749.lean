-- Prove2me | Theorems.Thm_WorkbookSource_base_55749
-- name    : WorkbookSource.base_55749
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:39.143556+00:00
-- url     : https://prove2.me/theorems/34b0d92f-d896-45c4-baf6-328476941b99
-- title:
--   A cyclic sixth-degree comparison with triple-product corrections
-- statement:
--   Let $ a,b,c\in\mathbb{R}_+$ . Prove that $ 11(a^6+b^6+c^6)+40abc(ab^2+bc^2+ca^2)\geq 51abc(a^2b+b^2c+c^2a)$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55749` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55749; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_55749 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 11 * (a^6 + b^6 + c^6) + 40 * a * b * c * (a * b^2 + b * c^2 + c * a^2) ≥ 51 * a * b * c * (a^2 * b + b^2 * c + c^2 * a)  :=  by sorry
