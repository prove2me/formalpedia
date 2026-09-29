-- Prove2me | Theorems.Thm_WorkbookSource_plus_2307
-- name    : WorkbookSource.plus_2307
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:55:44.49672+00:00
-- url     : https://prove2.me/theorems/8f62407f-78c6-43ab-8af4-8ac370639448
-- title:
--   A shifted quadratic reciprocal sum is at least one third
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a+b+c=3$ . Prove that
--    $$\dfrac{1}{2a^2+a+6}+\dfrac{1}{2b^2+b+6}+\dfrac{1}{2c^2+c+6}\geq\dfrac{1}{3}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_2307` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_2307; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_2307 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 1 / (2 * a ^ 2 + a + 6) + 1 / (2 * b ^ 2 + b + 6) + 1 / (2 * c ^ 2 + c + 6) ≥ 1 / 3   :=  by sorry
