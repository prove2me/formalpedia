-- Prove2me | Theorems.Thm_lean_workbook_plus_26586
-- name    : lean_workbook_plus_26586
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/c7bb22a7-f9ee-44af-b430-d98b5eaae176
-- statement:
--   Prove that $x=\sum_{k=1}^{\infty} \frac{a_k}{2^k}$ where $a_k \in \{ 0, 1 \}, \forall k \in \mathbb{N}$ for $x \in [0, 1)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26586 (x : ℝ) (hx : 0 ≤ x ∧ x < 1) : ∃ a : ℕ → ℝ, a = fun k => (x * 2 ^ k) % 1   :=  by sorry
