-- Prove2me | Theorems.Thm_lean_workbook_plus_51682
-- name    : lean_workbook_plus_51682
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/185e6528-dc48-4518-932d-136bb8b01927
-- statement:
--   Given that $x^{n}y^{n} = (xy)^{n}$ , for some integer $n \geq 2$ , prove that $x^{n-1}y^{n-1} = (yx)^{n-1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51682 (x y : ℤ) (n : ℕ) (h₁ : 2 ≤ n) (h₂ : x^n * y^n = (x * y)^n) : x^(n-1) * y^(n-1) = (y * x)^(n-1)   :=  by sorry
