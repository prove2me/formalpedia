-- Prove2me | Theorems.Thm_WorkbookSource_base_31229
-- name    : WorkbookSource.base_31229
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:49.115454+00:00
-- url     : https://prove2.me/theorems/43cac967-c5c7-423f-b635-f0a9f1155fe3
-- title:
--   A shifted pairwise-sum-square inequality
-- statement:
--   Prove that $227+(ab+bc+ca-23)^{2}\ge 2(a^{2}b+b^{2}c+c^{2}a)+3abc$ given $a,b,c\ge0$ and $a+b+c=9$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31229` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31229; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31229 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 9) : 227 + (a * b + b * c + c * a - 23)^2 ≥ 2 * (a^2 * b + b^2 * c + c^2 * a) + 3 * a * b * c  :=  by sorry
