-- Prove2me | solution 1 for lean_workbook_plus_64996
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:45.439952+00:00
-- url     : https://prove2.me/submissions/50f1ae0f-ab94-4910-92e0-02c369638ce0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) (A : Fin n → Set ℝ) (hA : ∀ i, A i ⊆ Set.Ioi 0) : ⋃ i, A i ⊆ Set.Ioi 0 := by
  (intros; simp_all)
