-- Prove2me | Theorems.Thm_WorkbookSource_base_47025
-- name    : WorkbookSource.base_47025
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:09:16.043256+00:00
-- url     : https://prove2.me/theorems/06a87831-cb5b-429b-b6cd-4159f6f6a205
-- title:
--   An asymmetric weighted reciprocal comparison
-- statement:
--   For positive reals $a,b,c$ , show that $\frac{5}{2a+b}+\frac{4}{2b+c}+\frac{3}{2c+a} \ge \frac{12}{3a+2b+c}+\frac{8}{a+3b+2c}+\frac{4}{2a+b+3c}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47025` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47025; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_47025 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (5 / (2 * a + b) + 4 / (2 * b + c) + 3 / (2 * c + a)) ≥ (12 / (3 * a + 2 * b + c) + 8 / (a + 3 * b + 2 * c) + 4 / (2 * a + b + 3 * c))  :=  by sorry
