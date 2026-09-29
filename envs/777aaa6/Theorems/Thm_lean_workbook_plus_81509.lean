-- Prove2me | Theorems.Thm_lean_workbook_plus_81509
-- name    : lean_workbook_plus_81509
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b6c433dc-2fea-4191-9cdc-36e55e345080
-- statement:
--   Let $a$ be a positive integer. Suppose that $\forall n$, $\exists d$, $d\not =1$, $d\equiv 1\pmod n$, $d\mid n^2a-1$. Prove that $a$ is a perfect square.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81509 {a : ℕ} (ha : 0 < a) (h : ∀ n : ℕ, ∃ d : ℕ, d ∣ n^2 * a - 1 ∧ d ≠ 1 ∧ d ≡ 1 [ZMOD n]) : ∃ b : ℕ, b^2 = a   :=  by sorry
