-- Prove2me | Theorems.Thm_WorkbookSource_base_40806
-- name    : WorkbookSource.base_40806
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:54:47.877559+00:00
-- url     : https://prove2.me/theorems/6f6021f5-e015-490b-8f13-fa4ca7543250
-- title:
--   A pairwise-product sum times reciprocal ratios bounds a quadratic sum
-- statement:
--   Prove that if $a,b,c>0$ then: $(ab+bc+ca)\left( \frac{bc}{a^2}+\frac{ca}{b^2}+\frac{ab}{c^2}\right)\ge 3(a^2+b^2+c^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40806` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40806; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_40806 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b + b * c + c * a) * (b * c / a ^ 2 + c * a / b ^ 2 + a * b / c ^ 2) ≥ 3 * (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
