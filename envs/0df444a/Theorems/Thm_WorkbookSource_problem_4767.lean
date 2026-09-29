-- Prove2me | Theorems.Thm_WorkbookSource_problem_4767
-- name    : WorkbookSource.problem_4767
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:11:12.387292+00:00
-- url     : https://prove2.me/theorems/b34889e1-c965-40b2-bb1c-cad6323061f7
-- title:
--   The alternating sum of a positive binomial row
-- statement:
--   Prove that, $\binom{n}{0}-\binom{n}{1}+\binom{n}{2}.......(-1)^n\binom{n}{n}=0$ Where n>0
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4767` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved. Notation repair: Replaced legacy ∑ i in s binder notation with current ∑ i ∈ s; no binder/domain/proposition change.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4767; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_4767 (n : ℕ) (h : n > 0) : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ)^k * choose n k = 0  :=  by sorry
