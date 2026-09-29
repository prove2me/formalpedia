-- Prove2me | Theorems.Thm_lean_workbook_plus_82357
-- name    : lean_workbook_plus_82357
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/fd2a0925-d9eb-4c56-ad88-135df0a13860
-- statement:
--   Let $z_1$ , $z_2$ and $z_3$ be three such complex numbers. We set $a=z_1-z_2$ , $b=z_2-z_3$ and $c=z_3-z_1$ . Obviously, $a+b+c=0$ and the given condition: $z_1^2+z_2^2+z_3^2=z_1z_2+z_2z_3+z_3z_1$ , is equivalent to $a^2+b^2+c^2=0$ . Hence $\left(a+b+c\right)^2=0=a^2+b^2+c^2+2\left(ab+bc+ca\right)$ so $ab+bc+ca=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82357  (z₁ z₂ z₃ : ℂ)
  (h₀ : z₁^2 + z₂^2 + z₃^2 = z₁ * z₂ + z₂ * z₃ + z₃ * z₁) :
  (z₁ - z₂) * (z₂ - z₃) + (z₂ - z₃) * (z₃ - z₁) + (z₃ - z₁) * (z₁ - z₂) = 0   :=  by sorry
