-- Prove2me | Theorems.Thm_lean_workbook_plus_13248
-- name    : lean_workbook_plus_13248
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/6f284570-0925-4c3c-a1f6-27513d00bd7a
-- statement:
--   Let $A_0, A_1,$ and $A_2$ be real numbers such that $-1\le A_0 + A_1x + A_2 x^2 \le 2$ holds for all real numbers $x$ that satisfies $-1\le x \le 1$ . Prove that $-3\le A_2 \le 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13248 (A0 A1 A2 : ℝ) (hA : ∀ x : ℝ, -1 ≤ x ∧ x ≤ 1 → -1 ≤ A0 + A1 * x + A2 * x ^ 2 ∧ A0 + A1 * x + A2 * x ^ 2 ≤ 2) : -3 ≤ A2 ∧ A2 ≤ 3   :=  by sorry
