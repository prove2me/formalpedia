-- Prove2me | Theorems.Thm_lean_workbook_plus_31342
-- name    : lean_workbook_plus_31342
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/d68e587e-5257-41e5-8ed5-90e1ad0890c5
-- statement:
--   $\frac{1}{a+b+1}+\frac{1}{b+c+1}+\frac{1}{c+a+1}\ge1\Leftrightarrow 2(a+b+c+1)\geq(a+b)(a+c)(b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31342 : ∀ a b c : ℝ, (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≥ 1 ↔ 2 * (a + b + c + 1) ≥ (a + b) * (a + c) * (b + c))   :=  by sorry
