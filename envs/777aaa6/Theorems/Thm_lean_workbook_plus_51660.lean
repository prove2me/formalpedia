-- Prove2me | Theorems.Thm_lean_workbook_plus_51660
-- name    : lean_workbook_plus_51660
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/f735649c-94c9-4a95-9f48-233f0d869623
-- statement:
--   Prove the following equalities of sets: \n $ \text{i)} \{x\in \mathbb{R}\ |\ \log_2 \lfloor x \rfloor = \lfloor \log_2 x\rfloor \} = \bigcup_{m\in \mathbb{N}} \left[2^m,2^m + 1\right)$ \n \n $ \text{ii)} \{x\in \mathbb{R}\ |\ 2^{\lfloor x\rfloor} = \left\lfloor 2^x\right\rfloor \} = \bigcup_{m\in \mathbb{N}} \left[m, \log_2 (2^m + 1) \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51660 : {x : ℝ | Real.logb 2 ⌊x⌋ = ⌊Real.logb 2 x⌋} = ⋃ m : ℕ, Set.Icc (2^m) (2^m + 1)   :=  by sorry
