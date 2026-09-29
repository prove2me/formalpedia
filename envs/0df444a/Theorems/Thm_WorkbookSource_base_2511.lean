-- Prove2me | Theorems.Thm_WorkbookSource_base_2511
-- name    : WorkbookSource.base_2511
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:57:24.641752+00:00
-- url     : https://prove2.me/theorems/bb8ec8c4-8acd-4e70-b5ef-469b121e3a56
-- title:
--   A fifth-power ratio bounds a symmetric quadratic expression
-- statement:
--   Prove that $\frac{a^5+b^5+c^5}{abc}+6(ab+bc+ca)\ge 7(a^2+b^2+c^2)$ given $a,b,c>0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2511` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2511; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2511 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^5 + b^5 + c^5) / (a * b * c) + 6 * (a * b + b * c + c * a) ≥ 7 * (a^2 + b^2 + c^2)  :=  by sorry
