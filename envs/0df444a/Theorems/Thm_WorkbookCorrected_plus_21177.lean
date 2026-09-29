-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_21177
-- name    : WorkbookCorrected.plus_21177
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T13:12:13.597017+00:00
-- url     : https://prove2.me/theorems/0fb03fcf-98dc-4ffc-a623-ac66103db90a
-- title:
--   The minimum squared distance under a shifted product constraint
-- statement:
--   For real numbers $x,y$ satisfying $(x+1)(y+1)=9$, the minimum of $x^2+y^2$ is $8$, attained at $(x,y)=(2,2)$.
--
--   Formalization Note: The original source asks for an extremum, while its formal statement supplied only a bound. This complete formulation includes both the universal bound and existence of an attaining point.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_21177 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_21177; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_21177 : (∀ x y : ℝ, (x+1)*(y+1)=9 → 8 ≤ x^2+y^2) ∧
    (∃ x y : ℝ, (x+1)*(y+1)=9 ∧ x^2+y^2=8) := by sorry
