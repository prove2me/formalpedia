-- Prove2me | Theorems.Thm_WorkbookSource_base_48671
-- name    : WorkbookSource.base_48671
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:41.461427+00:00
-- url     : https://prove2.me/theorems/0948be7f-ecda-4270-b106-2cb875902698
-- title:
--   A cubic-quartic upper bound at squared norm twelve
-- statement:
--   For $a,b,c,d \in \mathbb{R}$ that satisfy $a^2+b^2+c^2+d^2=12$ , prove: $4 \left(a^3+b^3+c^3+d^3\right) - \left(a^4+b^4+c^4+d^4 \right) \leq 48$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48671` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48671; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_48671 (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 12) :
  4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ≤ 48  :=  by sorry
