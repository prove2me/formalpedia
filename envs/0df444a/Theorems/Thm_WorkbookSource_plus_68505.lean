-- Prove2me | Theorems.Thm_WorkbookSource_plus_68505
-- name    : WorkbookSource.plus_68505
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:20:32.247686+00:00
-- url     : https://prove2.me/theorems/0f7df880-ad81-42b2-b5e4-db14c057c57c
-- title:
--   A rational function is not idempotent
-- statement:
--   Prove that the function $f(x)=\frac{x}{1-x}$ is not idempotent.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_68505` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_68505; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_68505 (f : ℝ → ℝ) (hf: f = fun x => x / (1 - x)) : ¬ (f ∘ f) = f   :=  by sorry
