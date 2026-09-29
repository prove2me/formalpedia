-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_41583
-- name    : WorkbookSyntax.plus_41583
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:00:48.794199+00:00
-- url     : https://prove2.me/theorems/2443fc54-a847-4bdf-a6eb-60b18fa00b80
-- title:
--   A short sum of doubled integers
-- statement:
--   $\sum_{x=1}^{3}2x=12$.
--
--   Notation repair: Replaced the obsolete finite-sum binder “in” with the current “∈” notation. The ranges, summands, hypotheses and conclusion are unchanged.
--
--   Source: Lean-Workbook record `lean_workbook_plus_41583` (Apache-2.0). [Original declaration](https://prove2.me/theorems/a0d1c60c-ed72-4cab-be5a-b3efaeee0f8e).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_41583; finite-sum notation repair; Apache-2.0

import Mathlib
open Nat

theorem WorkbookSyntax.plus_41583 : ∑ x ∈ Finset.Icc 1 3, 2 * x = 12   :=  by sorry
