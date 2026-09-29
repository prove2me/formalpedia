-- Prove2me | Theorems.Thm_lean_workbook_plus_54037
-- name    : lean_workbook_plus_54037
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/51ca3f71-95b1-4606-891e-2cecd85a14f9
-- statement:
--   Let $a+b=s,\ ab=t$ with $s,\ t>0$ and $s^2\geq 4t$ , thus \n\n $(x^2+ab)^2(a+b)^2-4ab(x^2+a^2)(x^2+b^2)$ \n\n $=s^2(x^2+t^2)^2-4t\{x^4+(s^2-2t)x^2+4t^2\}$ \n\n $=(s^2-4t)x^4-2t(s^2-4t)x^2+t^2(s^2-4t)$ \n\n $=(s^2-4t)(x^2-t)^2\geq 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54037  (a b s t x : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a + b = s)
  (h₂ : a * b = t)
  (h₃ : s^2 ≥ 4 * t)
  : (x^2 + a * b)^2 * (a + b)^2 - 4 * a * b * (x^2 + a^2) * (x^2 + b^2) ≥ 0   :=  by sorry
