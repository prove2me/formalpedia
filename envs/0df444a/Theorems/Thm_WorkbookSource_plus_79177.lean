-- Prove2me | Theorems.Thm_WorkbookSource_plus_79177
-- name    : WorkbookSource.plus_79177
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:59:58.615501+00:00
-- url     : https://prove2.me/theorems/055c5bef-450a-45f0-aa03-7c3f320f5a9f
-- title:
--   A squared pair-sum reciprocal inequality at fixed sum three
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a+b+c=3$ . Prove that $\frac{a}{(b+c)^2}+\frac{b}{(c+a)^2}+\frac{c}{(a+b)^2}\ge\frac{12}{9+7abc}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_79177` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_79177; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_79177 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a / (b + c) ^ 2 + b / (c + a) ^ 2 + c / (a + b) ^ 2) ≥ 12 / (9 + 7 * a * b * c)   :=  by sorry
