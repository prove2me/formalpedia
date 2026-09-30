-- Prove2me | solution 1 for lean_workbook_plus_2278
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:18:54.977123+00:00
-- url     : https://prove2.me/submissions/ce9fc719-6464-476a-9360-4c2eebaa5d70

import Mathlib.Analysis.Complex.Basic

theorem solution (p : ℕ) (hp : 5 ≤ p) (hp' : Nat.Prime p) :
  ∃ q : ℕ, p < q ∧ q < 2 * p - 2 :=
  ⟨p + 1, by omega, by omega⟩
