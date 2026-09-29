-- Prove2me | Theorems.Thm_lean_workbook_plus_52659
-- name    : lean_workbook_plus_52659
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/e81e0fd0-0c67-4aa4-9224-e99fb1b26707
-- statement:
--   ab+bc+ca=1\Longleftrightarrow a(b+c)=1-bc$ etc, \n \n the given inequality can be rewritten as $ \frac{1-bc}{b+c}+\frac{1-ca}{c+a}+\frac{1-ab}{a+b}\geq \sqrt{3}\Longleftrightarrow a+b+c\geq \sqrt{3}$ , \n \n which is true from $(a+b+c)^2\geq 3\Longleftrightarrow (a+b+c)^2\geq 3(ab+bc+ca)\Longleftrightarrow (a-b)^2+(b-c)^2+(c-a)^2\geq 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52659  (a b c : ℝ) :
  a * b + b * c + c * a = 1 ↔ a * (b + c) = 1 - b * c   :=  by sorry
