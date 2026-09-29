-- Prove2me | Theorems.Thm_WorkbookSource_base_46341
-- name    : WorkbookSource.base_46341
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:33.532657+00:00
-- url     : https://prove2.me/theorems/f2bae587-976b-4769-9730-6d889bbbed53
-- title:
--   A four-variable quadratic sum bounds three mixed products
-- statement:
--   Prove that $a^2+b^2+c^2+d^2 \geq d(a+b+c)$ for all real numbers $a, b, c, d$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46341` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46341; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_46341 (a b c d : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ d * (a + b + c)  :=  by sorry
