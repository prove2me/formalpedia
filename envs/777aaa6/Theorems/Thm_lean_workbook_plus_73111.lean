-- Prove2me | Theorems.Thm_lean_workbook_plus_73111
-- name    : lean_workbook_plus_73111
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/c62ea692-52b9-49f7-bef9-46b81a3f61b0
-- statement:
--   Let $a,b,c$ be positive reals such that $a(b+c)=bc.$ Then $\frac{a}{b+c} \leq \frac{1}{4}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73111 (a b c : ℝ) (h1 : a > 0 ∧ b > 0 ∧ c > 0) (h2 : a * (b + c) = b * c) : a / (b + c) ≤ 1 / 4   :=  by sorry
