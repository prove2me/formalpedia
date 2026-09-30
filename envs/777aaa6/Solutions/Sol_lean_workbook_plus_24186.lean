-- Prove2me | solution 1 for lean_workbook_plus_24186
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:14:45.33473+00:00
-- url     : https://prove2.me/submissions/0542f92c-e821-4bda-b2a7-52761e97a74b

import Mathlib.Analysis.Complex.Basic

theorem solution : BddAbove (Set.range (fun n : ℕ => (1/2)^n)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨n, rfl⟩
  simp only
  cases n with
  | zero => simp
  | succ m => simp
