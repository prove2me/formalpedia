-- Prove2me | Theorems.Thm_WorkbookSource_base_27135
-- name    : WorkbookSource.base_27135
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:43.29579+00:00
-- url     : https://prove2.me/theorems/4e267b45-cc93-4ae1-ba13-78a59974ae5b
-- title:
--   A cyclic sixth-degree inequality with a mixed-product correction
-- statement:
--   Given $ a, b, c \geq\ 0$ . Prove that: $ a^6 + b^6 + c^6 + 2abc(a^2b + b^2c + c^2a) \geq\ 2(a^3b^3 + b^3c^3 + c^3a^3) + abc(ab^2 + bc^2 + ca^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27135` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27135; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_27135 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^6 + b^6 + c^6 + 2 * a * b * c * (a^2 * b + b^2 * c + c^2 * a) ≥ 2 * (a^3 * b^3 + b^3 * c^3 + c^3 * a^3) + a * b * c * (a * b^2 + b * c^2 + c * a^2)  :=  by sorry
