-- Prove2me | Theorems.Thm_WorkbookSource_problem_24926
-- name    : WorkbookSource.problem_24926
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:52:12.626619+00:00
-- url     : https://prove2.me/theorems/b0d0c993-a748-4a59-a279-38e0577de37e
-- title:
--   A strict square-sum bound at sum one half
-- statement:
--   take $ a=x+y$ , $ b=y+z$ and $ c=z+x$ , $ x,y,z>0$ and $ x+y+z=\frac{1}2$ . So, your inequalitie is transformed into
--    $ (x+y)^{2}+(y+z)^{2}+(z+x)^{2}<\frac{1}2$
--    $ 2x^{2}+2y^{2}+2z^{2}+2xy+2yz+2zx=x^{2}+y^{2}+z^{2}+(x+y+z)^{2}<\frac{1}2$
--   So, it's equivalent to
--    $ x^{2}+y^{2}+z^{2}<\frac{1}4$
--   Using the fact that for positive numbers
--    $ x^{2}+y^{2}<(x+y)^{2}$
--   we have the desired result.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24926` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24926; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_24926  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x + y + z = 1 / 2) :
  x^2 + y^2 + z^2 < 1 / 4  :=  by sorry
