-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_43171
-- name    : WorkbookSyntax.plus_43171
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:00:03.818176+00:00
-- url     : https://prove2.me/theorems/d1e017be-0f30-4906-a0c8-ef57a0883ead
-- title:
--   Counting multiples of two, three or five
-- statement:
--   Exactly1,469 integers in $\{1,\ldots,2004\}$ are divisible by at least one of2,3 or5.
--
--   Notation repair: Replaced the obsolete finite-sum binder “in” with the current “∈” notation. The ranges, summands, hypotheses and conclusion are unchanged.
--
--   Source: Lean-Workbook record `lean_workbook_plus_43171` (Apache-2.0). [Original declaration](https://prove2.me/theorems/73f80333-581d-4fd8-ac2f-13ce914b0148).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_43171; finite-sum notation repair; Apache-2.0

import Mathlib
open Nat

theorem WorkbookSyntax.plus_43171 : ∑ k ∈ Finset.filter (λ x => 2∣x ∨ 3∣x ∨ 5∣x) (Finset.Icc 1 2004), 1 = 1469   :=  by sorry
