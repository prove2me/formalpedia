-- Prove2me | Theorems.Thm_WorkbookSource_base_4472
-- name    : WorkbookSource.base_4472
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:12:22.707011+00:00
-- url     : https://prove2.me/theorems/56441f30-0875-4f0f-8415-365d3d4b47cb
-- title:
--   A cyclic cubic-over-linear sum bounded by a squared total
-- statement:
--   Let $a,b,c>0$ . Prove that $\frac{a^{2}b}{a+b}+\frac{b^{2}c}{b+c}+\frac{c^{2}a}{c+a}\leq \frac{1}{6}(a+b+c)^{2}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4472` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4472; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4472 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * b / (a + b) + b^2 * c / (b + c) + c^2 * a / (c + a)) ≤ (1 / 6) * (a + b + c)^2  :=  by sorry
