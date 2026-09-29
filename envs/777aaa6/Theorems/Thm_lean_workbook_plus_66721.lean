-- Prove2me | Theorems.Thm_lean_workbook_plus_66721
-- name    : lean_workbook_plus_66721
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/1ffc9020-9602-472d-90f4-17a37c961886
-- statement:
--   If $n=3k$ the numbers $a_0=a_3=a_6\dots =a_{3k-3}=n$ , $a_1=a_4=a_7=\dots=a_{3k-2}=1$ , $a_2=a_5=a_8=\dots=a_{3k-1}=1$ build a $n$-ring.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66721 (n : ℕ) (hn : n % 3 = 0) (a : ℕ → ℕ) (ha : a = fun i ↦ if i % 3 = 0 then n else if i % 3 = 1 then 1 else 1) : ∃ k : ℕ, a k = n ∧ ∃ l : ℕ, a l = 1 ∧ ∃ m : ℕ, a m = 1   :=  by sorry
