-- Prove2me | solution 1 for fermat_little_p
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:36:16.952483+00:00
-- url     : https://prove2.me/submissions/978c4c90-830f-4513-9b03-291d5b682567

import Theorems.Thm_fermat_little_p
import Mathlib.Data.Int.Basic
import Mathlib.FieldTheory.Finite.Basic

theorem solution (p : ℕ) (hp : p.Prime) (a : ℤ) : (p : ℤ) ∣ a ^ p - a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : ((a ^ p - a : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.pow_card, sub_self]
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
