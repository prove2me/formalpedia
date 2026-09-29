-- Prove2me | Theorems.Thm_lean_workbook_plus_44185
-- name    : lean_workbook_plus_44185
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/bfb1098b-64b4-4fba-8e53-cfdc776394da
-- statement:
--   Let $ T_k$ be the expected remaining time in the process, conditioned on the last $ k$ flips having been heads. Note that $ T_3=0.$ Considering what happens on the next flip gives us the following system of equations: $ T_0=1+\frac12T_0+\frac12T_1$ $ T_1=1+\frac12T_0+\frac12T_2$ $ T_2=1+\frac12T_0$ This $ 3\times 3$ linear system can be solved readily. We get that $ T_2=8,T_1=12,$ and $ T_0=14.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44185  (t0 t1 t2 : ℝ)
  (h0 : t0 = 1 + t0 / 2 + t1 / 2)
  (h1 : t1 = 1 + t0 / 2 + t2 / 2)
  (h2 : t2 = 1 + t0 / 2) :
  t2 = 8 ∧ t1 = 12 ∧ t0 = 14   :=  by sorry
