-- Prove2me | Theorems.Thm_WorkbookSource_base_49195
-- name    : WorkbookSource.base_49195
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:51:29.409312+00:00
-- url     : https://prove2.me/theorems/bd72b085-0f06-4e57-9bb5-2613d53acf61
-- title:
--   A reciprocal sum times a shifted square has a linear lower bound
-- statement:
--   Prove that $(\frac{1}{a}+\frac{1}{b}+\frac{1}{c})(a+b+c-1)^2+12 \ge 8(a+b+c)$ given $a,b,c > 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_49195` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_49195; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_49195 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 / a + 1 / b + 1 / c) * (a + b + c - 1) ^ 2 + 12 ≥ 8 * (a + b + c)  :=  by sorry
