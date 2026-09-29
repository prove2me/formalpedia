-- Prove2me | Theorems.Thm_lean_workbook_plus_56800
-- name    : lean_workbook_plus_56800
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/5fb21664-dee8-41f0-9e55-c15e137cbf38
-- statement:
--   Let $a \in \mathbb{N^{*}}$ so that $a + 1$ is not a power of $2$ . Prove that there exist infinitely many $n \in \mathbb{N^{*}}$ such that $n \mid a^{n} + 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56800 (a : ℕ) (ha : ¬ ∃ k : ℕ, a + 1 = 2 ^ k) : ∃ n : ℕ, n ∣ a ^ n + 1   :=  by sorry
