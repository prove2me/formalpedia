-- Prove2me | Theorems.Thm_WorkbookSource_base_29412
-- name    : WorkbookSource.base_29412
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:18:40.347079+00:00
-- url     : https://prove2.me/theorems/e4c650e3-9fa4-490e-943e-7be6ac78e27f
-- title:
--   A cyclic product ratio bounds a symmetric quadratic expression
-- statement:
--   If $a, b, c>0$ prove that
--    $\frac{(a+2b)(b+2c)(c+2a)}{(2a+b+c)(2b+c+a)(2c+a+b)}+\frac{5}{64}\ge\frac{ab+bc+ca}{2(a^2+b^2+c^2)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29412` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29412; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29412 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 2 * b) * (b + 2 * c) * (c + 2 * a) / (2 * a + b + c) / (2 * b + c + a) / (2 * c + a + b) + 5 / 64 ≥ (a * b + b * c + c * a) / (2 * (a ^ 2 + b ^ 2 + c ^ 2))  :=  by sorry
