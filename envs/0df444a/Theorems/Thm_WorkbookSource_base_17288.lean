-- Prove2me | Theorems.Thm_WorkbookSource_base_17288
-- name    : WorkbookSource.base_17288
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:25:53.762893+00:00
-- url     : https://prove2.me/theorems/499430ec-828f-440a-b50a-7ce51e4910b8
-- title:
--   A cyclic shifted ratio with a pairwise-product correction
-- statement:
--   Let $a,b,c$ is positive real number satisfy $a+b+c=3$ prove that
--    $\frac{a}{b+c^2}+\frac{b}{c+a^2}+\frac{c}{a+b^2}+\frac{ab+bc+ca}{72} \ge \frac{37}{24}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17288` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17288; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17288 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a / (b + c ^ 2) + b / (c + a ^ 2) + c / (a + b ^ 2) + (a * b + b * c + c * a) / 72) ≥ 37 / 24  :=  by sorry
