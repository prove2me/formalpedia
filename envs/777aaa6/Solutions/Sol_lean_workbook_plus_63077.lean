-- Prove2me | solution 1 for lean_workbook_plus_63077
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:20:16.861037+00:00
-- url     : https://prove2.me/submissions/80e8dfc3-57a2-4ff7-bdd2-bb0ccbafd25d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (p : ℕ) (hp : p.Prime) (m : ℤ) : (∃ n : ℕ, (n : ℤ)^2 = m * p) ↔ ∃ t : ℤ, t^2 = m * p   := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨t, ht⟩
    refine ⟨t.natAbs, ?_⟩
    simpa only [Int.natCast_natAbs, sq_abs] using ht
