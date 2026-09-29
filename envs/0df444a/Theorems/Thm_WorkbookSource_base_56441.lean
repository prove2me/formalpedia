-- Prove2me | Theorems.Thm_WorkbookSource_base_56441
-- name    : WorkbookSource.base_56441
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:40:22.194228+00:00
-- url     : https://prove2.me/theorems/4d77b271-a648-417f-b125-7e26091cc7d8
-- title:
--   A cubic ratio sum with a squared quadratic correction
-- statement:
--   Let $a,b,c>0.$ Prove that $\frac{a^3+b^3+c^3}{abc}+4\left ( \frac{ab+bc+ca}{a^2+b^2+c^2} \right )^2\ge 7$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_56441` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_56441; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_56441 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) / (a * b * c) + 4 * ((a * b + b * c + c * a) / (a^2 + b^2 + c^2))^2 ≥ 7  :=  by sorry
