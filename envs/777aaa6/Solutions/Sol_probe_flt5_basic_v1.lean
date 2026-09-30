-- Prove2me | solution 1 for probe_flt5_basic_v1
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:33:30.513801+00:00
-- url     : https://prove2.me/submissions/8984d2b6-7c61-464c-82ba-1f3aac160bbf

import Mathlib.NumberTheory.FLT.Basic
import Theorems.Thm_flt_five

/-- `FermatLastTheoremFor 5` unfolds to
`∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 5 + b ^ 5 ≠ c ^ 5`, which is the platform theorem
`flt_five` stated with `0 < a` in place of `a ≠ 0`. -/
theorem solution : FermatLastTheoremFor 5 := by
  intro a b c ha hb hc
  exact flt_five a b c (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hc)
