-- Prove2me | Theorems.Thm_lean_workbook_plus_15893
-- name    : lean_workbook_plus_15893
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/279b2860-cc0c-469f-9b0c-ea41a68c1416
-- statement:
--   Let $ a,b,c\in \mathbb{R}$ such that $ ab + bc + ca\le 0$ . Show that:\n $ a^2b^2 + b^2c^2 + c^2a^2 + abc(a + b + c)\ge ab(a^2 + b^2) + bc(b^2 + c^2) + ca(c^2 + a^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15893 :  ∀ a b c : ℝ, a * b + b * c + c * a ≤ 0 → a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + a * b * c * (a + b + c) ≥ a * b * (a^2 + b^2) + b * c * (b^2 + c^2) + c * a * (c^2 + a^2)   :=  by sorry
