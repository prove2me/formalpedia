-- Prove2me | Theorems.Thm_lean_workbook_plus_12389
-- name    : lean_workbook_plus_12389
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/826ce98b-5f47-4a45-b304-c9f25bdb0f97
-- statement:
--   $\frac{a^{2}(a^{3}-1)}{a^{3}+1} \ge \frac{3(a-1)}{2} \Longleftrightarrow \frac{2a^{2}(a-1)(a^2+a+1)}{a^{3}+1} \ge 3(a-1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12389 : ∀ a : ℝ, a ≠ -1 ∧ a ≠ 1 → a^2 * (a^3 - 1) / (a^3 + 1) ≥ 3 * (a - 1) / 2 ↔ 2 * a^2 * (a - 1) * (a^2 + a + 1) / (a^3 + 1) ≥ 3 * (a - 1)   :=  by sorry
