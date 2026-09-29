-- Prove2me | Theorems.Thm_lean_workbook_plus_59539
-- name    : lean_workbook_plus_59539
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/101465ab-a637-4b6e-896f-63fb5ec2412e
-- statement:
--   Let Mr. Micolas Flamel be $x$ years old and let Mr. Licolas Flamel be $y$ years old. Then we have $x+103=2(y+103)$ and $x-13=6(y-13)$. Expanding the first equation gives $x+103=2y+206$, or $x=2y+103$. Plugging in gives $2y+90=6y-78$, or $y=42$. Hence $x=187$. So (a) is $187$ and (b) is $42$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59539  (x y : ℕ)
  (h₀ : x + 103 = 2 * (y + 103))
  (h₁ : x - 13 = 6 * (y - 13)) :
  x = 187 ∧ y = 42   :=  by sorry
