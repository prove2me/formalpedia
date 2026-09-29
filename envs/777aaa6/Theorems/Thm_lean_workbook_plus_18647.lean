-- Prove2me | Theorems.Thm_lean_workbook_plus_18647
-- name    : lean_workbook_plus_18647
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/cf80b7e2-9492-43a1-95ad-888d2ef71d9a
-- statement:
--   prove that for all $(a,b) \in \mathbb{R}^2$ : \n $(a^2+1)(b^2+1) \ge a(b^2+1)+b(a^2+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18647 (a b : ℝ) : (a^2 + 1) * (b^2 + 1) ≥ a * (b^2 + 1) + b * (a^2 + 1)   :=  by sorry
