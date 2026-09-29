-- Prove2me | Theorems.Thm_WorkbookSource_problem_19231
-- name    : WorkbookSource.problem_19231
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:04:58.187571+00:00
-- url     : https://prove2.me/theorems/165186de-635c-4d54-8f63-b65fe70dc8ad
-- title:
--   A quadratic bound for cosine
-- statement:
--   Now, $ \cos A(1 - \cos A)\le \frac 14\ \Longleftrightarrow\ \cos A - \cos^2 A - \frac 14\le 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19231` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19231; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_19231 : ∀ A : ℝ, Real.cos A * (1 - Real.cos A) ≤ 1 / 4  :=  by sorry
