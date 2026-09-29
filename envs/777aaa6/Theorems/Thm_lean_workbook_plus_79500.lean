-- Prove2me | Theorems.Thm_lean_workbook_plus_79500
-- name    : lean_workbook_plus_79500
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/7a03fbcf-3945-4f97-bd47-55926a7c7b8a
-- statement:
--   $a,b,c,x,y,z >0$. $ax+by+cz=xyz \Leftrightarrow \frac{a}{yz}+\frac{b}{xz}+\frac{c}{xy}=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79500 (a b c x y z : ℝ) : a>0 ∧ b>0 ∧ c>0 ∧ x>0 ∧ y>0 ∧ z>0 → (a * x + b * y + c * z = x * y * z ↔ a / y / z + b / x / z + c / x / y = 1)   :=  by sorry
