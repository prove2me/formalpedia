-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_44151
-- name    : WorkbookSyntax.plus_44151
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:00:18.880855+00:00
-- url     : https://prove2.me/theorems/087a3f21-fab8-4df3-91a5-c69b8eb7d24d
-- title:
--   A reciprocal sum below one
-- statement:
--   $\sum_{k=997}^{1995}1/k<1$.
--
--   Notation repair: Replaced the obsolete finite-sum binder “in” with the current “∈” notation. The ranges, summands, hypotheses and conclusion are unchanged.
--
--   Source: Lean-Workbook record `lean_workbook_plus_44151` (Apache-2.0). [Original declaration](https://prove2.me/theorems/9c35320d-562f-4f67-b525-0d6622f770d8).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_44151; finite-sum notation repair; Apache-2.0

import Mathlib
open Nat

theorem WorkbookSyntax.plus_44151 : ∑ k ∈ Finset.Icc (997 : ℕ) 1995, (1 : ℝ) / k < 1   :=  by sorry
