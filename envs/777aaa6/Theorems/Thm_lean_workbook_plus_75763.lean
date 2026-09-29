-- Prove2me | Theorems.Thm_lean_workbook_plus_75763
-- name    : lean_workbook_plus_75763
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/bfa2cc2c-41e3-4603-9979-39430d32e8bd
-- statement:
--   Prove the Lemma: If $a \vert b$ and $a \vert c$ then $a \vert (mb - nc)$ where $a,b,c,m,n$ are integers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75763 (a b c m n : ℤ) (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ (m * b - n * c)   :=  by sorry
