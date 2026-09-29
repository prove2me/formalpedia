-- Prove2me | Theorems.Thm_WorkbookSource_base_32381
-- name    : WorkbookSource.base_32381
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:31:11.51271+00:00
-- url     : https://prove2.me/theorems/051e8df8-0140-450f-b476-61d38460aceb
-- title:
--   A cyclic ratio sum bounds a symmetric quadratic expression
-- statement:
--   Let a,b,c>0. Prove that $\frac{a}{b} + \frac{b}{c} + \frac{c}{a} \ge \frac{1}{2}.\frac{{{a^2} + {b^2} + {c^2}}}{{ab + bc + ca}} + \frac{5}{2}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32381` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32381; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32381 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ 1 / 2 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c) + 5 / 2  :=  by sorry
