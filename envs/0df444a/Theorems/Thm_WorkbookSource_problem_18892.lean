-- Prove2me | Theorems.Thm_WorkbookSource_problem_18892
-- name    : WorkbookSource.problem_18892
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:11:47.840105+00:00
-- url     : https://prove2.me/theorems/bdecd0a1-bf34-411a-926f-5d1e013097f3
-- title:
--   A finite sum of ones
-- statement:
--   Explain why $\sum_{l=0}^{n-1}1=n$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18892` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved. Notation repair: Replaced legacy ∑ i in s binder notation with current ∑ i ∈ s; no binder/domain/proposition change.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18892; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_18892 (n : ℕ) : ∑ l ∈ (Finset.range n), 1 = n  :=  by sorry
