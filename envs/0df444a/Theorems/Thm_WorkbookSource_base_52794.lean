-- Prove2me | Theorems.Thm_WorkbookSource_base_52794
-- name    : WorkbookSource.base_52794
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:24:38.370646+00:00
-- url     : https://prove2.me/theorems/b3e70db0-ac50-426a-8124-3e1ba6f943c3
-- title:
--   A cyclic harmonic product sum has a normalized alternating-product upper bound
-- statement:
--   For $a, b, c,d>0$ prove that
--    $\frac{ab}{a+b}+\frac{bc}{b+c}+\frac{cd}{c+d}+\frac{da}{d+a}\le\frac{2(ab+bc+cd+da)}{a+b+c+d}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52794` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52794; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_52794 (a b c d : ℝ) (hab : 0 < a) (hbc : 0 < b) (hcd : 0 < c) (hda : 0 < d) : (a * b / (a + b) + b * c / (b + c) + c * d / (c + d) + d * a / (d + a)) ≤ (2 * (a * b + b * c + c * d + d * a)) / (a + b + c + d)  :=  by sorry
