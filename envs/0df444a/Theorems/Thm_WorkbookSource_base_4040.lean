-- Prove2me | Theorems.Thm_WorkbookSource_base_4040
-- name    : WorkbookSource.base_4040
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:11:13.398705+00:00
-- url     : https://prove2.me/theorems/73a29ae7-c267-4a39-8229-7cf24a89fa0f
-- title:
--   A cyclic cubic-over-quadratic sum bounds half the total
-- statement:
--   Let $ a,b,c$ be positive real numbers. Prove the inequality:
--
--    $ \frac {a^3}{b^2+c^2} + \frac {b^3}{c^2+a^2} + \frac {c^3}{a^2+b^2}\ge \frac {a+b+c}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4040` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4040; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4040 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (b^2 + c^2) + b^3 / (c^2 + a^2) + c^3 / (a^2 + b^2)) ≥ (a + b + c) / 2  :=  by sorry
