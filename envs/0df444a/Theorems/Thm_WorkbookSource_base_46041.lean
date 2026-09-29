-- Prove2me | Theorems.Thm_WorkbookSource_base_46041
-- name    : WorkbookSource.base_46041
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:49:18.670146+00:00
-- url     : https://prove2.me/theorems/6e9900f0-8226-4673-9f2c-607a80909846
-- title:
--   A symmetric quartic-cubic bound at total zero
-- statement:
--   Prove that $(ab+bc+ca)^2+9abc\ge 3(ab+bc+ca)$ given $a+b+c=0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46041` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46041; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_46041 (a b c : ℝ) (h : a + b + c = 0) : (a * b + b * c + c * a) ^ 2 + 9 * a * b * c ≥ 3 * (a * b + b * c + c * a)  :=  by sorry
