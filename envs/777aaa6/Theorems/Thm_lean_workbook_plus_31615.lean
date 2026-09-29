-- Prove2me | Theorems.Thm_lean_workbook_plus_31615
-- name    : lean_workbook_plus_31615
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/73903122-5e5e-4470-8fa0-fddce92c21db
-- statement:
--   for $10^n +3$ we consider both side mod 3. $10^n+3 \equiv 1 \mod 3$ ,
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31615 : ∀ n:ℕ, (10^n + 3) % 3 = 1   :=  by sorry
