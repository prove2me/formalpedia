-- Prove2me | Theorems.Thm_lean_workbook_plus_19963
-- name    : lean_workbook_plus_19963
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/7146f042-039d-48f5-814a-cf4a78622624
-- statement:
--   Assuming the inequality holds for some $ k \in \mathbb{N}$, $ k \geqslant 2$, prove it for $ k + 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19963 (k : ℕ) (h₁ : 2 ≤ k) (h₂ : 3 ^ k ≥ 2 ^ k * k) : 3 ^ (k + 1) ≥ 2 ^ (k + 1) * (k + 1)   :=  by sorry
