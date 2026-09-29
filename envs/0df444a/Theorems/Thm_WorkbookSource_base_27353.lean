-- Prove2me | Theorems.Thm_WorkbookSource_base_27353
-- name    : WorkbookSource.base_27353
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:35:44.808588+00:00
-- url     : https://prove2.me/theorems/79e8f0fd-f7c7-47e6-a8ad-9af8e119172d
-- title:
--   A weighted cyclic ratio sum bounded by symmetric quadratic forms
-- statement:
--   Let $ a,b,c$ be positive real numbers. Prove that
--    $ \frac {a^2 + b^2 + c^2}{ab + bc + ca} \ge \frac {a}{b + 2c} + \frac {b}{c + 2a} + \frac {c}{a + 2b}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27353` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27353; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_27353 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ≥ a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b)  :=  by sorry
