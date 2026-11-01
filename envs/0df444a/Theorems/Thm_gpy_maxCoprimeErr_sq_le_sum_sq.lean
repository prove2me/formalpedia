-- Prove2me | Theorems.Thm_gpy_maxCoprimeErr_sq_le_sum_sq
-- name    : gpy_maxCoprimeErr_sq_le_sum_sq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T02:27:30.10014+00:00
-- url     : https://prove2.me/theorems/a49c195a-7d1b-4e82-9fd2-01497f823385
-- title:
--   Squared max coprime-residue error is at most the summed squared errors
-- statement:
--   Unconditional bridge lemma: at one modulus, the squared maximum coprime-residue error is at most the sum of the squared errors over all coprime residues, since the attained residue is one nonnegative term of the sum. All local definitions are unfolded into Mathlib terms.
-- source:
--   GPY genuine-BDH conditional reduction (GPYBDHFull.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_maxCoprimeErr_sq_le_sum_sq (M : ℕ → ℕ → ℝ) (Y L : ℕ) :
    ((if h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs (((((Finset.range (Y + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y L))).Nonempty then
    (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs (((((Finset.range (Y + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y L))).max' h
    else 0)) ^ 2 ≤
      ∑ r ∈ (Finset.range L).filter (fun r => Nat.Coprime r L),
        (abs (((((Finset.range (Y + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y L)) ^ 2 := by sorry
