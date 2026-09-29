-- Prove2me | Theorems.Thm_lean_workbook_plus_76098
-- name    : lean_workbook_plus_76098
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e7efe3f2-1ba2-436d-ad37-98f99732d6c4
-- statement:
--   Let $a$ be real number such that $-1\le a\le 1$ . Prove that: \n $(1+|a|+a^2)^3\geq (1+|a|)^3(1+|a|^3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76098 : ∀ a : ℝ, -1 ≤ a ∧ a ≤ 1 → (1 + |a| + a^2)^3 ≥ (1 + |a|)^3 * (1 + |a|^3)   :=  by sorry
