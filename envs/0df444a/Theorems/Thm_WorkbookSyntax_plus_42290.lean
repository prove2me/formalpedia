-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_42290
-- name    : WorkbookSyntax.plus_42290
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:00:50.907749+00:00
-- url     : https://prove2.me/theorems/97a19e0a-a283-4989-8c9b-ba36375085b6
-- title:
--   A sum of residues of powers of two
-- statement:
--   $\sum_{k=0}^{19}(2^k\bmod25)=250$.
--
--   Notation repair: Replaced the obsolete finite-sum binder “in” with the current “∈” notation. The ranges, summands, hypotheses and conclusion are unchanged.
--
--   Source: Lean-Workbook record `lean_workbook_plus_42290` (Apache-2.0). [Original declaration](https://prove2.me/theorems/f8d0f62a-6488-4a17-ba27-74f31d807f12).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_42290; finite-sum notation repair; Apache-2.0

import Mathlib
open Nat

theorem WorkbookSyntax.plus_42290 :
  ∑ k ∈ (Finset.range 20), (2^k) % 25 = 250   :=  by sorry
