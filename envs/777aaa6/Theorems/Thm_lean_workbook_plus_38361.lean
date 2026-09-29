-- Prove2me | Theorems.Thm_lean_workbook_plus_38361
-- name    : lean_workbook_plus_38361
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/ecfe76a0-b8fe-41ac-9907-95f1c84f76b8
-- statement:
--   Prove that $ |cosa| + |cosb| \ge |sin(a + b)|$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38361 (a b : ℝ) : |Real.cos a| + |Real.cos b| ≥ |Real.sin (a + b)|   :=  by sorry
