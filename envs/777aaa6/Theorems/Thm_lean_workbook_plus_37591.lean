-- Prove2me | Theorems.Thm_lean_workbook_plus_37591
-- name    : lean_workbook_plus_37591
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/c1ab863d-337c-4cf3-b701-c15a9e31dd8d
-- statement:
--   Prove the identity: $\sin 2x = 2\sin x \cos x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37591 x : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x   :=  by sorry
