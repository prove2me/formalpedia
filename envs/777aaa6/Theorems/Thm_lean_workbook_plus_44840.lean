-- Prove2me | Theorems.Thm_lean_workbook_plus_44840
-- name    : lean_workbook_plus_44840
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/c8b869fb-e546-430b-be9c-5311a4ced736
-- statement:
--   Prove that for all $x \ge 0, \cos{x} = \sin(\frac{\pi}{2} - x)$ and $\sin{x} \le x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44840 (x : ℝ) (hx : 0 ≤ x) : Real.cos x = Real.sin (Real.pi / 2 - x)   :=  by sorry
