-- Prove2me | Theorems.Thm_lean_workbook_plus_17492
-- name    : lean_workbook_plus_17492
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/49ffd6d6-28b4-4762-9db4-14a099169455
-- statement:
--   Does there exist a function, $f:\mathbb{N} \rightarrow \mathbb{N}$, where $f(f(n))+n=2009, \forall n \in \mathbb{N}$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17492 (f : ℕ → ℕ) (hf: ∃ n, f (f n) + n = 2009) : ∃ n, f (f n) + n = 2009   :=  by sorry
