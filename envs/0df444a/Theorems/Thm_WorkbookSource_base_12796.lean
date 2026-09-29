-- Prove2me | Theorems.Thm_WorkbookSource_base_12796
-- name    : WorkbookSource.base_12796
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:46:04.36592+00:00
-- url     : https://prove2.me/theorems/5d3d30de-b46e-4c86-aae5-bcd964931672
-- title:
--   A quartic-cubic-quadratic power-sum inequality at total one
-- statement:
--   If $a,b,c$ be real numbers such that $a+b+c=1$ , then $1+18\sum a^4+6\sum a^2 \ge 24\sum a^3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12796` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12796; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12796 (a b c : ℝ) (habc : a + b + c = 1) : 1 + 18 * (a ^ 4 + b ^ 4 + c ^ 4) + 6 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 24 * (a ^ 3 + b ^ 3 + c ^ 3)  :=  by sorry
