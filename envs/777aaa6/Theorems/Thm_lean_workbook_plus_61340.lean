-- Prove2me | Theorems.Thm_lean_workbook_plus_61340
-- name    : lean_workbook_plus_61340
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/9c02949a-15e6-4259-9308-b6cb3beada50
-- statement:
--   So $f(x)=0$ $\forall x\le 0$ . And so $f(x)=x$ $\forall x\ge 0$ . And so $f(x)=\max(x,0)$ , which indeed is a solution . $-f(-x)$ is then $\min(x,0)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61340 (x : ℝ) : max x 0 = if x ≤ 0 then 0 else x   :=  by sorry
