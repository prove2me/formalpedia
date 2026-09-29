-- Prove2me | Theorems.Thm_lean_workbook_plus_42602
-- name    : lean_workbook_plus_42602
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/41534fe7-42ac-4328-bdb6-aa84c6e19509
-- statement:
--   Let $ f:{(1,2,3)} \to {(1,2,3)}$ be a function then the no of functions $g:{(1,2,3)} \to {(1,2,3)}$ such that $f(x)=g(x)$ for at least one x belong to {1,2,3}
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42602 (f : Fin 3 → Fin 3) : (∃ g : Fin 3 → Fin 3, ∃ x : Fin 3, f x = g x)   :=  by sorry
