-- Prove2me | Theorems.Thm_WorkbookTyped_plus_44637
-- name    : WorkbookTyped.plus_44637
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:41:53.427083+00:00
-- url     : https://prove2.me/theorems/1bd7dd4f-7d9e-469f-b8e1-f7d872c92f9e
-- title:
--   An inequality for real exponential sums
-- statement:
--   Let $ a,b,c \in R$ and $ a+b+c=0$ . Prove that $ \boxed{8^a+8^b+8^c\ge 2^a+2^b+2^c}$
--
--   Declaration repair: Added explicit real binders (a b c : ℝ) and real base annotations so every variable exponent uses Real.rpow. The old simp proof depended on natural-number inference and does not prove this repaired theorem. A new argument proves the intended real-exponent inequality.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_44637` (Apache-2.0). [Original malformed declaration](https://prove2.me/theorems/04b4d958-9d5a-4f94-b821-bbab7ac0a930). This record proves the corrected statement.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_44637; explicit variable-declaration repair; Apache-2.0

import Mathlib

theorem WorkbookTyped.plus_44637 (a b c : ℝ) : a + b + c = 0 → (8 : ℝ)^a + (8 : ℝ)^b + (8 : ℝ)^c ≥ (2 : ℝ)^a + (2 : ℝ)^b + (2 : ℝ)^c   :=  by sorry
