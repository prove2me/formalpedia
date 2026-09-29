-- Prove2me | Theorems.Thm_WorkbookSource_plus_34031
-- name    : WorkbookSource.plus_34031
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:22.076653+00:00
-- url     : https://prove2.me/theorems/7d56bd8f-b190-4893-8cc6-6191c2b807ef
-- title:
--   A quartic bound from its coefficients
-- statement:
--   We have $b \geq \frac{a^2+c^2}{4}$ so $$x^4+ax^3+bx^2+cx+1 =\left(x+\frac{a}{2}\right)^2x^2-\frac{a^2}{4}x^2 + \left(\frac{c}{2}x+1\right)^2-\frac{c^2}{4}x^2 + bx^2$$ $$=\left(x+\frac{a}{2}\right)^2x^2 +\left(\frac{c}{2}x+1\right)^2+\left(b-\frac{a^2}{4}-\frac{c^2}{4}\right)x^2 \geq 0$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_34031` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_34031; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_34031  (a b c x : ℝ)
  (h₀ : b ≥ (a^2 + c^2) / 4) :
  x^4 + a * x^3 + b * x^2 + c * x + 1 ≥ 0   :=  by sorry
