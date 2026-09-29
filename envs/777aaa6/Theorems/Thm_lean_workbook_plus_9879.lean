-- Prove2me | Theorems.Thm_lean_workbook_plus_9879
-- name    : lean_workbook_plus_9879
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2938f866-3419-4bf5-99ad-52da8ab37e94
-- statement:
--   Put $u:=\sqrt{2x+19}\implies 2x=u^2-19$ , hence the equation becomes \n \n $2u^2-14[u]+21=0\iff u^2-7[u]+{21\over 2}=0$ \n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9879  (x : ℝ)
  (u : ℝ)
  (h₀ : 0 ≤ 2 * x + 19)
  (h₁ : u = Real.sqrt (2 * x + 19))
  (h₂ : 2 * u^2 - 14 * u + 21 = 0) :
  u^2 - 7 * u + 21 / 2 = 0   :=  by sorry
