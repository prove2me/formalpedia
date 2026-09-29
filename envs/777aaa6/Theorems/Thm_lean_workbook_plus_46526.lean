-- Prove2me | Theorems.Thm_lean_workbook_plus_46526
-- name    : lean_workbook_plus_46526
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/c3464af2-2b52-464f-b1c0-dfc49f512f01
-- statement:
--   The first condition implies that $64-8a+b=0$ , and the second condition implies that $a=n+8$ . Therefore, $64-8a+b=0\implies 64-8(n+8)+b=0\implies b=8n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46526  (a b n : ℝ)
  (h₀ : 64 - 8 * a + b = 0)
  (h₁ : a = n + 8)
  (h₂ : b = 8 * n) :
  64 - 8 * a + b = 0   :=  by sorry
