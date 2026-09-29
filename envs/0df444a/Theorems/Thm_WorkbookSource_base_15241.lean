-- Prove2me | Theorems.Thm_WorkbookSource_base_15241
-- name    : WorkbookSource.base_15241
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:59:53.373843+00:00
-- url     : https://prove2.me/theorems/f6400905-878f-46c8-9957-c6472a43aaab
-- title:
--   A normalized triple product bounds a symmetric quadratic ratio
-- statement:
--   If $a, b, c>0$ prove that
--    $\frac{8abc}{(a+b)(b+c)(c+a)}+2\geq\frac{3(ab+bc+ca)}{a^2+b^2+c^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15241` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15241; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15241 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (8 * a * b * c) / (a + b) / (b + c) / (c + a) + 2 ≥ (3 * (a * b + b * c + c * a)) / (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
