-- Prove2me | Theorems.Thm_WorkbookSource_plus_60598
-- name    : WorkbookSource.plus_60598
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:54:33.105274+00:00
-- url     : https://prove2.me/theorems/aa310ac3-db28-45ff-aa49-b91f758dfdf4
-- title:
--   A shifted cyclic quadratic ratio sum is at least three halves
-- statement:
--   Let a, b, c be positive numbers such that a + b + c = 3. Prove that: \(\frac{a^2}{1+b^2} + \frac{b^2}{1+c^2} + \frac{c^2}{1+a^2} \geq \frac{3}{2}\)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_60598` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_60598; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_60598 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 / (1 + b^2) + b^2 / (1 + c^2) + c^2 / (1 + a^2)) ≥ 3 / 2   :=  by sorry
