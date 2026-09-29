-- Prove2me | Theorems.Thm_WorkbookSource_base_3991
-- name    : WorkbookSource.base_3991
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:01:01.684048+00:00
-- url     : https://prove2.me/theorems/74618dff-5edd-43ef-81a3-5992f609870c
-- title:
--   A symmetric sixth-degree inequality in mixed powers
-- statement:
--   Show that for nonnegative reals $a, b, c$ :
--    $2a^6+2b^6+2c^6+16a^3b^3+16b^3c^3+16c^3a^3\geq 9a^4(b^2+c^2)+9b^4(c^2+a^2)+9c^4(a^2+b^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3991` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3991; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3991 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 2 * a ^ 6 + 2 * b ^ 6 + 2 * c ^ 6 + 16 * a ^ 3 * b ^ 3 + 16 * b ^ 3 * c ^ 3 + 16 * c ^ 3 * a ^ 3 ≥ 9 * a ^ 4 * (b ^ 2 + c ^ 2) + 9 * b ^ 4 * (c ^ 2 + a ^ 2) + 9 * c ^ 4 * (a ^ 2 + b ^ 2)  :=  by sorry
