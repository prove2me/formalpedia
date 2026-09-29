-- Prove2me | Theorems.Thm_WorkbookSource_base_33447
-- name    : WorkbookSource.base_33447
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:29:43.364631+00:00
-- url     : https://prove2.me/theorems/a41c726d-a835-4110-ad33-fd62943ae837
-- title:
--   A mixed quadratic reciprocal upper bound
-- statement:
--   Prove that $\frac{1}{a^2+2bc}+\frac{1}{b^2+2ca}+\frac{1}{c^2+2ab}\leq \frac{1}{3}\left(\frac{1}{ab}+\frac{1}{bc}+\frac{1}{ca}\right)$ given $a,b,c>0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33447` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33447; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33447 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (a ^ 2 + 2 * b * c) + 1 / (b ^ 2 + 2 * c * a) + 1 / (c ^ 2 + 2 * a * b) ≤ 1 / 3 * (1 / (a * b) + 1 / (b * c) + 1 / (c * a))  :=  by sorry
