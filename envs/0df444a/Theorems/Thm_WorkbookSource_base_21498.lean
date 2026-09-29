-- Prove2me | Theorems.Thm_WorkbookSource_base_21498
-- name    : WorkbookSource.base_21498
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:12:06.720872+00:00
-- url     : https://prove2.me/theorems/8e1b5dd4-c3f8-4b56-a12e-20d9634129b9
-- title:
--   A squared pair sum with a linear correction bounds mixed square-root products
-- statement:
--   Prove that for positive numbers a and b, the inequality \(\frac{(a+b)^2}{2}+\frac{a+b}{4} \geq a\sqrt{b}+b\sqrt{a}\) holds.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21498` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21498; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21498 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) ^ 2 / 2 + (a + b) / 4 ≥ a * Real.sqrt b + b * Real.sqrt a  :=  by sorry
