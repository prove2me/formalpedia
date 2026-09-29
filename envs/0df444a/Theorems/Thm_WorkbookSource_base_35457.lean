-- Prove2me | Theorems.Thm_WorkbookSource_base_35457
-- name    : WorkbookSource.base_35457
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:52:05.375974+00:00
-- url     : https://prove2.me/theorems/e5a18324-1406-4794-8d70-d791cdb0d0b1
-- title:
--   A cyclic fifth-power sum times the total bounds a squared product
-- statement:
--   Is this true? $a,b,c \in \mathbb{R}^+$
--
--   $$\left(a+b+c\right)\left(a^2b^3+b^2c^3+c^2a^3\right)\ge 3\left(abc\right)^2 $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35457` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35457; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35457 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) * (a^2 * b^3 + b^2 * c^3 + c^2 * a^3) ≥ 3 * (a * b * c)^2  :=  by sorry
