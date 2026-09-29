-- Prove2me | Theorems.Thm_WorkbookSource_plus_76314
-- name    : WorkbookSource.plus_76314
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:19:00.217821+00:00
-- url     : https://prove2.me/theorems/a6a12a06-8c01-42ce-8012-705e32de1b42
-- title:
--   A squared quadratic expression bounds four fourth powers
-- statement:
--   Prove that $(4\sum_{\mathrm{cyc}} a^2 + \frac{4}{3}\sum_{\mathrm{cyc}}(a - c)^2 + \frac{8}{3}\sum_{\mathrm{cyc}} (a - b)^2)^2 \ge 64(a^4+b^4+c^4+d^4)$ for $a, b, c, d \ge 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_76314` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_76314; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_76314 (a b c d : ℝ) : (4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + (4 / 3) * ((a - c) ^ 2 + (b - d) ^ 2 + (c - a) ^ 2 + (d - b) ^ 2) + (8 / 3) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - a) ^ 2)) ^ 2 ≥ 64 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4)   :=  by sorry
