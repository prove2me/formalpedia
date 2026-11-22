-- Prove2me | solution 1 for P2M_exp_zero_of_zpow_eq_one__f6bf2bc7dd54
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:54:49.478559+00:00
-- url     : https://prove2.me/submissions/4c45b5c2-b0e6-4404-a749-6004f6a36971

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc
import Theorems.Thm_exp_zero_of_pow_eq_one_aux

set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
theorem _root_.solution {n : ℤ} (ha : (0 : Γ₀) ^ n = 1) : n = 0 := by
  have haux (n : ℤ) (ha : (0 : Γ₀) ^ n = 1) (hn : n ≥ 0) : n = 0 := by
    have : n.toNat = 0 := by
      apply exp_zero_of_pow_eq_one_aux (Γ₀ := Γ₀)
      rwa [← zpow_natCast, Int.toNat_of_nonneg hn]
    rw [← Int.toNat_of_nonneg hn]
    simpa
  by_cases hn : n ≥ 0
  · exact haux n ha hn
  · apply Int.neg_eq_zero.mp
    apply haux
    · simpa
    · omega
