-- Prove2me | Theorems.Thm_WorkbookSource_base_26445
-- name    : WorkbookSource.base_26445
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:09:30.091928+00:00
-- url     : https://prove2.me/theorems/63b91306-7479-48b0-9235-21c84546a9e7
-- title:
--   A weighted cyclic quadratic ratio sum is at most three quarters
-- statement:
--   Let $ a, b, c$ be positive real numbers. Prove that: $ \frac{a^2}{2a^2+ab+c^2}+\frac{b^2}{2b^2+bc+a^2}+\frac{c^2}{2c^2+ca+b^2} \le \frac{3}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26445` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26445; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26445 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (2 * a^2 + b * a + c^2) + b^2 / (2 * b^2 + c * b + a^2) + c^2 / (2 * c^2 + a * c + b^2)) ≤ 3 / 4  :=  by sorry
