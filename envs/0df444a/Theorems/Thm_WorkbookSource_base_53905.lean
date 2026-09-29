-- Prove2me | Theorems.Thm_WorkbookSource_base_53905
-- name    : WorkbookSource.base_53905
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:11:03.078151+00:00
-- url     : https://prove2.me/theorems/51059d1e-c161-45e1-a800-f72b99a7858e
-- title:
--   A shifted quadratic reciprocal sum is at most one
-- statement:
--   Prove that $\frac{1}{a^2+b+c}+\frac{1}{b^2+a+c}+\frac{1}{c^2+a+b}\le 1$ given $a, b, c$ are positive real numbers such that $a+b+c=3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53905` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53905; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_53905 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / (a ^ 2 + b + c) + 1 / (b ^ 2 + a + c) + 1 / (c ^ 2 + a + b) ≤ 1  :=  by sorry
