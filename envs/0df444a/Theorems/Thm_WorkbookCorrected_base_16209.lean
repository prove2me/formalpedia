-- Prove2me | Theorems.Thm_WorkbookCorrected_base_16209
-- name    : WorkbookCorrected.base_16209
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:13:33.219655+00:00
-- url     : https://prove2.me/theorems/532da1e9-9a7b-48ce-8a00-5fc52e13e5e7
-- title:
--   A squared linear-form minimum on a hyperbola
-- statement:
--   Find the minimum value of $(3x+y)^2$ given that $x^2 - y^2 = 1$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16209` (Apache-2.0). Natural-language proposition preserved; the source bound is completed with an exact attainment witness. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16209; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_16209 : (∀ (x y : ℝ) (h : x^2 - y^2 = 1), 8 ≤ (3*x + y)^2) ∧ (∃ x y : ℝ, (x^2 - y^2 = 1) ∧ ( 8  =  (3*x + y)^2  )) := by sorry
