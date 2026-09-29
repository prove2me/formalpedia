-- Prove2me | Theorems.Thm_lean_workbook_plus_47563
-- name    : lean_workbook_plus_47563
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/a5a0ac2d-89dd-4496-8be1-955ab32b819b
-- statement:
--   $(x-2)(x-3)(x+1)=0 \Longrightarrow$ $x=3$ or $x=2$ or $x=-1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47563 (x : ℝ) (hx : (x-2)*(x-3)*(x+1) = 0) : x = 3 ∨ x = 2 ∨ x = -1   :=  by sorry
