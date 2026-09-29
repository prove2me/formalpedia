-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_61272
-- name    : WorkbookSyntax.plus_61272
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:19:51.114182+00:00
-- url     : https://prove2.me/theorems/7e7432b8-5004-4150-bb87-606a4f48d05c
-- title:
--   Lean-Workbook Syntax 61272: The sum of the first twenty cubes
-- statement:
--   $1^3+2^3+\cdots+20^3=44100$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_61272` (Apache-2.0), [original record](https://prove2.me/theorems/92302e2c-0956-40d9-a401-29ee4c4bbfa9). This corrected declaration replaces the obsolete finite sum/product binder `in` with `∈` and restores required imports or namespaces. Ranges, casts, quantifiers, and mathematical expressions are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_61272; immutable original Prove2Me node 92302e2c-0956-40d9-a401-29ee4c4bbfa9

import Mathlib.Algebra.BigOperators.Intervals

theorem WorkbookSyntax.plus_61272 : ∑ k ∈ Finset.range 21, k^3 = 44100   :=  by sorry
