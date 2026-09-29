-- Prove2me | Theorems.Thm_lean_workbook_plus_47398
-- name    : lean_workbook_plus_47398
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/20917f9b-c04f-4178-b427-d839f7d28b05
-- statement:
--   Squaring both sides of $\frac{c}{a}+\frac{a}{b}+\frac{b}{c}=-\frac{3}{2}$ we get $\frac{c^2}{a^2}+\frac{a^2}{b^2}+\frac{b^2}{c^2}+2\left(\frac{b}{a}+\frac{c}{b}+\frac{a}{c}\right)=\frac{9}{4}$ . So we are to prove $\frac{b^2}{a^2}+\frac{c^2}{b^2}+\frac{a^2}{c^2}\geqq \frac{9}{4}-(\frac{c^2}{a^2}+\frac{a^2}{b^2}+\frac{b^2}{c^2})$ . This is equivalent to $\frac{b^2}{a^2}+\frac{c^2}{b^2}+\frac{a^2}{c^2}+\frac{c^2}{a^2}+\frac{a^2}{b^2}+\frac{b^2}{c^2}\geqq \frac{9}{4}$ , which is obvious because by AM-GM $\frac{b^2}{a^2}+\frac{a^2}{b^2} \geq 2$ , $\frac{c^2}{b^2}+\frac{b^2}{c^2} \geq 2$ and $\frac{a^2}{c^2}+\frac{c^2}{a^2} \geq 2$ and hence $\frac{b^2}{a^2}+\frac{c^2}{b^2}+\frac{a^2}{c^2}+\frac{c^2}{a^2}+\frac{a^2}{b^2}+\frac{b^2}{c^2}\geqq 6> \frac{9}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47398  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c / a + a / b + b / c = -3 / 2) :
  b^2 / a^2 + c^2 / b^2 + a^2 / c^2 ≥ 9 / 4   :=  by sorry
