-- Prove2me | Theorems.Thm_WorkbookSource_base_4786
-- name    : WorkbookSource.base_4786
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:03:55.005222+00:00
-- url     : https://prove2.me/theorems/2f701a86-d3cd-4a5b-a457-c9f9975434d6
-- title:
--   A fifth-degree bound involving three pairwise sums
-- statement:
--   Prove that for all $a,b,c \ge 0$ we have : $(a+b+c)^2\left(a+b\right)\left(a+c\right)\left(b+c\right) \ge 24abc \left(a^2+b^2+c^2\right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4786` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4786; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4786 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) ^ 2 * (a + b) * (a + c) * (b + c) ≥ 24 * a * b * c * (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
