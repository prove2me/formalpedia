-- Prove2me | Theorems.Thm_WorkbookSource_base_41951
-- name    : WorkbookSource.base_41951
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:02:29.8839+00:00
-- url     : https://prove2.me/theorems/a1d7f1cb-38b6-4c97-97ea-2e55d6e9f0e9
-- title:
--   A shifted symmetric quadratic reciprocal upper bound at fixed sum three
-- statement:
--   Prove that
--   $\frac{1}{a^2+b^2+c+21}+\frac{1}{b^2+c^2+a+21}+\frac{1}{c^2+a^2+b+21} \le \frac{1}{8}$
--   Given $a,b,c > 0$ and $a+b+c=3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41951` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41951; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_41951 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 1 / (a ^ 2 + b ^ 2 + c + 21) + 1 / (b ^ 2 + c ^ 2 + a + 21) + 1 / (c ^ 2 + a ^ 2 + b + 21) ≤ 1 / 8  :=  by sorry
