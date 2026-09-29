-- Prove2me | Theorems.Thm_lean_workbook_plus_5366
-- name    : lean_workbook_plus_5366
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/0fe171fd-a6c6-4bcf-a783-bc3f143719df
-- statement:
--   prove that : $(\sin A+\sin B)^2+(\sin B+\sin C)^2+(\sin C+\sin A)^2\leq3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5366 : ∀ A B C : ℝ, (sin A + sin B) ^ 2 + (sin B + sin C) ^ 2 + (sin C + sin A) ^ 2 ≤ 3   :=  by sorry
