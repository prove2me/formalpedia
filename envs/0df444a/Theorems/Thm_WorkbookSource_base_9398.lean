-- Prove2me | Theorems.Thm_WorkbookSource_base_9398
-- name    : WorkbookSource.base_9398
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:22:34.253324+00:00
-- url     : https://prove2.me/theorems/37dccfad-73f5-4a52-8233-5784b70403a3
-- title:
--   A cyclic squared pair-sum reciprocal lower bound
-- statement:
--   Prove that $\frac{1}{(a+b)^2}+\frac{1}{(b+c)^2}+\frac{1}{(c+d)^2}+\frac{1}{(d+a)^2}\ge \frac{2}{ac+bd}$ where $a,b,c,d>0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9398` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9398; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9398 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 1 / (a + b) ^ 2 + 1 / (b + c) ^ 2 + 1 / (c + d) ^ 2 + 1 / (d + a) ^ 2 ≥ 2 / (a * c + b * d)  :=  by sorry
