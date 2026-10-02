-- Prove2me | solution 1 for BookSixth.mean_log_le_log_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T08:51:41.569379+00:00
-- url     : https://prove2.me/submissions/5c7576c7-9114-404c-94e4-904d02d30a06

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (r : Nat) (hr : 0 < r) :
    (∑ k ∈ Finset.Icc 1 r, Real.log (k : Real)) / (r : Real)
      ≤ Real.log (r : Real) := by
  have hrR : (0 : Real) < (r : Real) := by exact_mod_cast hr
  have hcard : (Finset.Icc 1 r).card = r := by rw [Nat.card_Icc]; omega
  have hle : ∑ k ∈ Finset.Icc 1 r, Real.log (k : Real)
      ≤ (Finset.Icc 1 r).card • Real.log (r : Real) := by
    apply Finset.sum_le_card_nsmul
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : (1 : Real) ≤ (k : Real) := by exact_mod_cast hk.1
    have h0 : (0 : Real) < (k : Real) := by linarith
    exact Real.log_le_log h0 (by exact_mod_cast hk.2)
  rw [hcard, nsmul_eq_mul] at hle
  rw [div_le_iff₀ hrR]
  calc (∑ k ∈ Finset.Icc 1 r, Real.log (k : Real))
      ≤ (r : Real) * Real.log (r : Real) := hle
    _ = Real.log (r : Real) * (r : Real) := mul_comm _ _
