-- Prove2me | Theorems.Thm_WorkbookTyped_plus_43951
-- name    : WorkbookTyped.plus_43951
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:41:52.17563+00:00
-- url     : https://prove2.me/theorems/19e3beab-01ab-4eef-b8e4-da9701a08139
-- title:
--   The two real roots of a quadratic
-- statement:
--   Solve for $x$: $x^2 - 2x - 1 = 0$
--
--   Declaration repair: Added the explicit real binder (x : ℝ). The original formula already uses Real.sqrt, which fixes the intended real equation once its variable is declared.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_43951` (Apache-2.0). [Original malformed declaration](https://prove2.me/theorems/c4eabcf4-12c7-4f22-a9cb-b80099ffcbc7). This record proves the corrected statement.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_43951; explicit variable-declaration repair; Apache-2.0

import Mathlib

theorem WorkbookTyped.plus_43951 (x : ℝ) : x^2 - 2*x - 1 = 0 ↔ x = 1 + Real.sqrt 2 ∨ x = 1 - Real.sqrt 2   :=  by sorry
