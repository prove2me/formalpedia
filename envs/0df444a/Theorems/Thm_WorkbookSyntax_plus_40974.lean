-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_40974
-- name    : WorkbookSyntax.plus_40974
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:59:51.018372+00:00
-- url     : https://prove2.me/theorems/957834cf-4fb4-4475-8a40-2e21f15939e2
-- title:
--   A bound for the first sixty-four reciprocals
-- statement:
--   $\sum_{i=1}^{64}1/i<6.4$.
--
--   Notation repair: Replaced the obsolete finite-sum binder “in” with the current “∈” notation. The ranges, summands, hypotheses and conclusion are unchanged.
--
--   Source: Lean-Workbook record `lean_workbook_plus_40974` (Apache-2.0). [Original declaration](https://prove2.me/theorems/db2c034e-85b2-4fd6-ac88-eae4c2dac865).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_40974; finite-sum notation repair; Apache-2.0

import Mathlib
open Nat

theorem WorkbookSyntax.plus_40974 : ∑ i ∈ Finset.Icc (1 : ℕ) 64, (1 : ℝ) / i < 6.4   :=  by sorry
