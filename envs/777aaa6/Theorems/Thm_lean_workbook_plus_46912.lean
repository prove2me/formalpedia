-- Prove2me | Theorems.Thm_lean_workbook_plus_46912
-- name    : lean_workbook_plus_46912
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/505835b6-208c-468a-acf4-d2b2e6d1fbc7
-- statement:
--   Note that $\sqrt{2+\sqrt{2+\sqrt{2}}} < \sqrt{2+\sqrt{2+\sqrt{2+\cdots}}}$ Denote the RHS to be $x$ . Note that $x>0$ . Then: $x = \sqrt{2+x}$ $x^2 = x+2$ $(x+1)(x-2)=0$ $x = 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46912  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x = Real.sqrt (2 + x)) :
  x = 2   :=  by sorry
