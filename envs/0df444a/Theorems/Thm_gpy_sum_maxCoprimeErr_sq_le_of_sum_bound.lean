-- Prove2me | Theorems.Thm_gpy_sum_maxCoprimeErr_sq_le_of_sum_bound
-- name    : gpy_sum_maxCoprimeErr_sq_le_of_sum_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T06:51:14.910677+00:00
-- url     : https://prove2.me/theorems/4a79b460-d847-44a4-91a2-5d4a3a04bac0
-- title:
--   Trivial second-moment lemma for max coprime errors
-- statement:
--   If the first moment of the max coprime-residue errors over moduli up to Q is at most B (with B nonnegative), then the second moment is at most B squared. This is the trivial second moment: each error is at most the whole first moment. It is a pure lemma with no analytic input, stated with all local definitions unfolded into Mathlib terms.
-- source:
--   GPY BDH-partial bounds (trivial second moment plus Cauchy-Schwarz with the tau-fourth bound), conditional on a plain BV sum bound; formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_sum_maxCoprimeErr_sq_le_of_sum_bound (M : ℕ → ℕ → ℝ) (Y' Q : ℕ) {B : ℝ}
    (hBnn : 0 ≤ B)
    (hsum : ∑ L ∈ Finset.range (Q + 1), (if h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).Nonempty then
    (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).max' h
    else 0) ≤ B) :
    ∑ L ∈ Finset.range (Q + 1), ((if h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).Nonempty then
    (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M Y' L))).max' h
    else 0)) ^ 2 ≤ B ^ 2 := by sorry
