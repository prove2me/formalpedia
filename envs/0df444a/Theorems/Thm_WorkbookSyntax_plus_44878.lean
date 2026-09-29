-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_44878
-- name    : WorkbookSyntax.plus_44878
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:00:51.844105+00:00
-- url     : https://prove2.me/theorems/7c6315a1-5404-4c06-86df-4012d8c81b10
-- title:
--   A finite binomial convolution
-- statement:
--   $\sum_{k=0}^{10}\binom{22}{10-k}\binom{15}{k}=348330136$.
--
--   Notation repair: Replaced the obsolete finite-sum binder “in” with the current “∈” notation. The ranges, summands, hypotheses and conclusion are unchanged.
--
--   Source: Lean-Workbook record `lean_workbook_plus_44878` (Apache-2.0). [Original declaration](https://prove2.me/theorems/a4ea265f-d12a-4bf1-ada0-3f25ca184c31).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_44878; finite-sum notation repair; Apache-2.0

import Mathlib
open Nat

theorem WorkbookSyntax.plus_44878 (h₁ : 0 < 22) (h₂ : 0 < 15) : ∑ k ∈ Finset.range 11, (Nat.choose 22 (10 - k) * Nat.choose 15 k) = 348330136   :=  by sorry
