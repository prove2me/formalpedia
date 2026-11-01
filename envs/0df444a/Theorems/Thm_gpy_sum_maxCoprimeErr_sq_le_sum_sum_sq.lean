-- Prove2me | Theorems.Thm_gpy_sum_maxCoprimeErr_sq_le_sum_sum_sq
-- name    : gpy_sum_maxCoprimeErr_sq_le_sum_sum_sq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T02:55:28.998025+00:00
-- url     : https://prove2.me/theorems/1369b2c9-498c-4aba-81b2-336b1b3f8394
-- title:
--   Second moment of max coprime errors is at most the summed squared-error second moment
-- statement:
--   Unconditional bridge summed over moduli: the second moment of the max coprime-residue errors is at most the summed squared-error second moment. All local definitions are unfolded into Mathlib terms.
-- source:
--   GPY genuine-BDH conditional reduction (GPYBDHFull.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_sum_maxCoprimeErr_sq_le_sum_sum_sq (M : ℕ → ℕ → ℝ) (Y Q : ℕ) :
    ∑ L ∈ Finset.range (Q + 1), ((if h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs (((((Finset.range (Y + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y L))).Nonempty then
    (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs (((((Finset.range (Y + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y L))).max' h
    else 0)) ^ 2 ≤
      ∑ L ∈ Finset.range (Q + 1), ∑ r ∈ (Finset.range L).filter
          (fun r => Nat.Coprime r L),
        (abs (((((Finset.range (Y + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y L)) ^ 2 := by sorry
