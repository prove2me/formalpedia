-- Prove2me | Theorems.Thm_lean_workbook_plus_17368
-- name    : lean_workbook_plus_17368
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/ef1261d0-671d-4f2d-9f73-162d235796ec
-- statement:
--   For some $4$ th degree polynomial $f (x)$ , the following is true: \n $\bullet$ $f (-1) = 1$ . \n $\bullet$ $f (0) = 2$ . \n $\bullet$ $f (1) = 4$ . \n $\bullet$ $f (-2) = f (2) = f (3)$ . Find $f (4)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17368 (f : ℝ → ℝ) (hf : f = fun x => x^4 + ax^3 + bx^2 + cx + d) : f (-1) = 1 ∧ f (0) = 2 ∧ f (1) = 4 ∧ f (-2) = f (2) ∧ f (2) = f (3) → f (4) = 17   :=  by sorry
