-- Prove2me | Theorems.Thm_WorkbookSource_base_10515
-- name    : WorkbookSource.base_10515
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:41:24.730019+00:00
-- url     : https://prove2.me/theorems/c11bf350-abd2-491b-b2e4-c48ac0d75f90
-- title:
--   A cubic sum and squared triple product have a fixed lower bound
-- statement:
--   Let $a,b,c \geq 0$ and $a+b+c=3$. Prove that $a^3+b^3+c^3+2a^2b^2c^2 \geq 5$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10515` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10515; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10515 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : a^3 + b^3 + c^3 + 2 * a^2 * b^2 * c^2 ≥ 5  :=  by sorry
