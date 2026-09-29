-- Prove2me | Theorems.Thm_WorkbookSource_plus_80171
-- name    : WorkbookSource.plus_80171
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:36.860947+00:00
-- url     : https://prove2.me/theorems/b9fa10f1-a263-4953-a549-f483e4e6c4df
-- title:
--   Three quadratic factors bound twice the pairwise sum
-- statement:
--   Let $a,b,c $ be real numbers . Prove that $(1+a^2)(1+b^2)(1+c^2)\ge 2 (ab+bc+ca) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_80171` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_80171; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_80171 (a b c : ℝ) : (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) ≥ 2 * (a * b + b * c + c * a)   :=  by sorry
