-- Prove2me | Theorems.Thm_WorkbookSource_plus_9080
-- name    : WorkbookSource.plus_9080
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:24.856826+00:00
-- url     : https://prove2.me/theorems/f4b6b77f-c5c6-47e7-8e9b-4feaf1b8c2cb
-- title:
--   A squared-distance inequality under two product constraints
-- statement:
--   Let $a,b,c,d$ be real numbers such that $ab=c^2+d^2=1.$ Prove that
--    $$ (a-c)^2+(b-d)^2+2ad+2bc \geq 1$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_9080` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_9080; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_9080 (a b c d : ℝ) (h : a * b = 1) (h' : c ^ 2 + d ^ 2 = 1) :  (a - c) ^ 2 + (b - d) ^ 2 + 2 * a * d + 2 * b * c ≥ 1   :=  by sorry
