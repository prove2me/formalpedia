-- Prove2me | Theorems.Thm_lean_workbook_plus_59081
-- name    : lean_workbook_plus_59081
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/40cae212-2b41-4fb8-bd7c-927407a0171f
-- statement:
--   Prove inductively that $ 6 | 7^{n} - 1$ for all $ n \in \mathbb{N^{*}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59081 (n : ℕ) (hn : 0 < n) : 6 ∣ 7^n - 1   :=  by sorry
