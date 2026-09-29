-- Prove2me | Theorems.Thm_lean_workbook_plus_26830
-- name    : lean_workbook_plus_26830
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/53758b18-d079-41a1-b8c4-16e29a20c2f5
-- statement:
--   Let $S=\{p/q| q\leq 2009, p/q <1257/2009, p,q \in \mathbb{N} \}$ . If the maximum element of $S$ is $p_0/q_0$ in reduced form, find $p_0+q_0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26830 (S : Finset ℚ) (hS : ∀ q : ℚ, q ∈ S ↔ q.den ≤ 2009 ∧ q < 1257 / 2009) : (∀ q : ℚ, q ∈ S → q.den ≤ 2009 ∧ q < 1257 / 2009) ∧ (∀ q : ℚ, q.den ≤ 2009 ∧ q < 1257 / 2009 → q ∈ S)  :=  by sorry
