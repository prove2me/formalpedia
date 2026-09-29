-- Prove2me | Theorems.Thm_lean_workbook_plus_886
-- name    : lean_workbook_plus_886
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/95a4c528-f45b-4594-8358-1aad1c4bb7e4
-- statement:
--   Prove the identity: $\sin { \left( x \right) } =2\sin { \frac { x }{ 2 } } \cos { \frac { x }{ 2 } } $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_886 : ∀ x, sin x = 2 * sin (x / 2) * cos (x / 2)   :=  by sorry
