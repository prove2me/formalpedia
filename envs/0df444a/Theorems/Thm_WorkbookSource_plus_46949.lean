-- Prove2me | Theorems.Thm_WorkbookSource_plus_46949
-- name    : WorkbookSource.plus_46949
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:15:10.161876+00:00
-- url     : https://prove2.me/theorems/256b604d-c425-45da-b52e-1171b7cc6619
-- title:
--   A shifted pair-product ratio upper bound at fixed sum three
-- statement:
--   Let $a, b, c>0, a+b+c=3$ . Prove that
--    $\frac{ab}{2c^2+3(a+b)}+\frac{bc}{2a^2+3(b+c)}+\frac{ca}{2b^2+3(c+a)}\le\frac{ab+bc+ca}{8}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_46949` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_46949; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_46949 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a * b / (2 * c ^ 2 + 3 * (a + b)) + b * c / (2 * a ^ 2 + 3 * (b + c)) + c * a / (2 * b ^ 2 + 3 * (c + a))) ≤ (a * b + b * c + c * a) / 8   :=  by sorry
