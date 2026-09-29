-- Prove2me | Theorems.Thm_lean_workbook_plus_71588
-- name    : lean_workbook_plus_71588
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/85153a54-f0c3-41b4-8ad3-f1496f38364e
-- statement:
--   Generalization. Prove that $ \boxed {\ \tan 3x\cdot\tan (30 - x)\cdot\tan (30 + x)\cdot\tan (90 - x)\ = \ 1\ }\ (*)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71588 : ∀ x : ℝ, tan 3*x * tan (30 - x) * tan (30 + x) * tan (90 - x) = 1   :=  by sorry
