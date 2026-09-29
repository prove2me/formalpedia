-- Prove2me | Theorems.Thm_lean_workbook_plus_42749
-- name    : lean_workbook_plus_42749
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/51ae5c67-fb44-41bd-973f-0e8eea46d9c0
-- statement:
--   prove that for all $(a,b) \in \mathbb{R}^2$ : \n $ (a^{2}+1)(b^{2}+1)\ge a(b^{2}+1)+b(a^{2}+1) $ \n $\Leftrightarrow \frac{a}{a^2+1}+\frac{b}{b^2+1} \le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42749 (a b : ℝ) : (a^2 + 1) * (b^2 + 1) ≥ a * (b^2 + 1) + b * (a^2 + 1) ↔ a / (a^2 + 1) + b / (b^2 + 1) ≤ 1   :=  by sorry
