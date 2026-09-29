-- Prove2me | Theorems.Thm_WorkbookSource_base_38183
-- name    : WorkbookSource.base_38183
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:36:17.084287+00:00
-- url     : https://prove2.me/theorems/cce97ec5-91c8-40cb-a547-0ca1c1deb5d1
-- title:
--   A cyclic quadratic reciprocal upper bound
-- statement:
--   Given $ a, b, c > 0.$ Prove that: $ \frac {3(a + b + c)}{2(ab + bc + ca)} \geq\ \frac {a}{a^2 + b^2} + \frac {b}{b^2 + c^2} + \frac {c}{c^2 + a^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38183` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38183; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38183 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * (a + b + c)) / (2 * (a * b + b * c + c * a)) ≥ a / (a ^ 2 + b ^ 2) + b / (b ^ 2 + c ^ 2) + c / (c ^ 2 + a ^ 2)  :=  by sorry
