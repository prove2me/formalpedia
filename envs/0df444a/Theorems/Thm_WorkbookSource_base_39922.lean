-- Prove2me | Theorems.Thm_WorkbookSource_base_39922
-- name    : WorkbookSource.base_39922
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:52:02.475583+00:00
-- url     : https://prove2.me/theorems/70e9f540-0a9d-4d6b-8a1a-27a8175eeb50
-- title:
--   A shifted cyclic quadratic ratio sum bounds a normalized total
-- statement:
--   Show that
--   a/(1+b^2)+b/(1+c^2)+c/(1+a^2) \\geq 3(a+b+c)/(3+a^2+b^2+c^2) for all positive a, b, c.
--
--   (AOPS is weird and doesn't let me use latex)
--
--   Let $ a, b, c$ be positive reals. Prove that
--
--    $$\\frac{a}{1+b^2}+\\frac{b}{1+c^2}+\\frac{c}{1+a^2}\\geq \\frac{3(a+b+c)}{3+a^2+b^2+c^2}$$ \\*
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39922` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39922; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_39922 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (1 + b ^ 2) + b / (1 + c ^ 2) + c / (1 + a ^ 2)) ≥ 3 * (a + b + c) / (3 + a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
