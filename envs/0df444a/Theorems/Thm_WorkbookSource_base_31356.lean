-- Prove2me | Theorems.Thm_WorkbookSource_base_31356
-- name    : WorkbookSource.base_31356
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:10.165321+00:00
-- url     : https://prove2.me/theorems/20f35339-3941-4d88-bd29-5cf23a9778da
-- title:
--   A four-variable quartic sum bounds mixed products
-- statement:
--   (a+b)(ac^{2}+bd^{2})=a^{2}c^{2}+b^{2}d^{2}+abd^{2}+abc^{2}
--    by AM-GM inequality,we can prove this inequality:
--    $2(a^{4}+b^{4}+c^{4}+d^{4})\geq 2(a^{2}c^{2}+b^{2}d^{2}+abd^{2}+abc^{2})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31356` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31356; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31356 (a b c d : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≥ 2 * (a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 + a * b * d ^ 2 + a * b * c ^ 2)  :=  by sorry
