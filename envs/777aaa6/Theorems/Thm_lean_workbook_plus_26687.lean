-- Prove2me | Theorems.Thm_lean_workbook_plus_26687
-- name    : lean_workbook_plus_26687
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/3659cc97-1984-4dbd-b4ac-1a579fad6f0c
-- statement:
--   Prove: If $ a, b \in \mathbb{Z}$ and $ n \in \mathbb{N}$ , prove that $ a \mod n = b \mod n \iff n|(a-b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26687 (a b n : ℤ) (hn : n ≠ 0) : a % n = b % n ↔ n ∣ a - b   :=  by sorry
