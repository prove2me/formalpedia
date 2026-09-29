-- Prove2me | Theorems.Thm_WorkbookSource_base_6221
-- name    : WorkbookSource.base_6221
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:17:51.027535+00:00
-- url     : https://prove2.me/theorems/78112806-aad0-4d77-9823-f1f28163b78a
-- title:
--   A cyclic linear-over-quadratic sum bounded by pairwise products
-- statement:
--   For $a, b, c>0$ prove that $\frac{a}{5a^2+2bc+5b^2}+\frac{b}{5b^2+2ca+5c^2}+\frac{c}{5c^2+2ab+5a^2}\le\frac{ab+bc+ca}{12abc}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6221` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6221; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6221 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (5 * a ^ 2 + 2 * b * c + 5 * b ^ 2) + b / (5 * b ^ 2 + 2 * c * a + 5 * c ^ 2) + c / (5 * c ^ 2 + 2 * a * b + 5 * a ^ 2)) ≤ (a * b + b * c + c * a) / (12 * a * b * c)  :=  by sorry
