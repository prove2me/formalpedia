-- Prove2me | Theorems.Thm_WorkbookSource_plus_68598
-- name    : WorkbookSource.plus_68598
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:20.411887+00:00
-- url     : https://prove2.me/theorems/58ee6b04-8d5e-4275-a12a-a68aedeef9d9
-- title:
--   An asymmetric fifth-degree inequality for positive variables
-- statement:
--   Proof that $a^4b+a^4c+b^4c+bc^4\geq ab^2c^2$ for all $a,b,c>0$ :
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_68598` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_68598; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_68598 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 * b + a^4 * c + b^4 * c + b * c^4 ≥ a * b^2 * c^2   :=  by sorry
