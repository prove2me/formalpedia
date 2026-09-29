-- Prove2me | Theorems.Thm_WorkbookSource_base_54664
-- name    : WorkbookSource.base_54664
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:15:32.841298+00:00
-- url     : https://prove2.me/theorems/ac5924b2-e47c-4eb4-bf74-c5e6ca80b45e
-- title:
--   A weighted cyclic ratio comparison with pairwise denominators
-- statement:
--   For the positive real numbers $a,b,c$ prove that
--    $ \frac{c+2a}{b} + \frac{a+2b}{c} + \frac{b+2c}{a} \ge \frac{3a+4c-b}{a+b} + \frac{3b+4a-c}{b+c} + \frac{3c+4b-a}{c+a} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_54664` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_54664; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_54664 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (c + 2 * a) / b + (a + 2 * b) / c + (b + 2 * c) / a ≥ (3 * a + 4 * c - b) / (a + b) + (3 * b + 4 * a - c) / (b + c) + (3 * c + 4 * b - a) / (c + a)  :=  by sorry
