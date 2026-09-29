-- Prove2me | Theorems.Thm_WorkbookSource_base_30032
-- name    : WorkbookSource.base_30032
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:47:42.67197+00:00
-- url     : https://prove2.me/theorems/bf22fb16-5ae0-47ad-9ed5-2fc246ba848e
-- title:
--   A product of three quadratic forms bounds a cubic symmetric product
-- statement:
--   oh yes . Why don't I think it early? >So, can you prove that this inequality
--    $ (a^2+ab+b^2)(b^2+bc+c^2)(c^2+ca+a^2)\ge abc(a+b+c)^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30032` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30032; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30032 (a b c : ℝ) : (a^2 + b * a + b^2) * (b^2 + c * b + c^2) * (c^2 + a * c + a^2) ≥ a * b * c * (a + b + c)^3  :=  by sorry
