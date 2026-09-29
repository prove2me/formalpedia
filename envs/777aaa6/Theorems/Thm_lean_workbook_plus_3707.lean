-- Prove2me | Theorems.Thm_lean_workbook_plus_3707
-- name    : lean_workbook_plus_3707
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/0c81f751-4c0d-4aa6-95fa-c8cde559646d
-- statement:
--   The second equation can be rewritten as $\frac{x^2+y^2}{xy}=\frac{25}{12}$ . Squaring the first equation we find that $x^2+2xy+y^2=49 \implies x^2+y^2=49-2xy$ . Substituting into our second equation, we have\n\n$\frac{49-2xy}{xy}=\frac{25}{12}$\n\n$\implies \frac{49}{xy}-2=\frac{25}{12}$\n\n$\implies \frac{49}{xy}=\frac{49}{12} \implies xy=12$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3707  (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x + y = 7)
  (h₂ : (x^2 + y^2) / (x * y) = 25 / 12) :
  x * y = 12   :=  by sorry
