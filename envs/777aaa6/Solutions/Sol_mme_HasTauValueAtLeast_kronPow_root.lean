-- Prove2me | solution 1 for mme_HasTauValueAtLeast_kronPow_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T05:03:08.844394+00:00
-- url     : https://prove2.me/submissions/ac684ee4-6b2d-486e-a752-b15dbc222cb1

import Theorems.Thm_mme_HasTauValueAtLeast_to_cofinal_finite_extractions
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions
import Theorems.Thm_mme_kronPow_kronPow_isomorphic

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    (T : TensorObj K 3) (tau V : ℝ) (r : ℕ)
    (hr : 0 < r) (hV : 0 ≤ V)
    (hpower : HasTauValueAtLeast (T.kronPow r) tau (V ^ r)) :
    HasTauValueAtLeast T tau V := by
  obtain ⟨s, error, hs, herror, _herror_pos, hextract⟩ :=
    mme_HasTauValueAtLeast_to_cofinal_finite_extractions
      (T.kronPow r) tau (V ^ r) hpower
  let s' : ℕ → ℕ := fun n => s n * r
  have hs' : Tendsto s' atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hs.eventually (eventually_ge_atTop b)] with n hn
    exact hn.trans (Nat.le_mul_of_pos_right (s n) hr)
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    T tau V hV s' hs' error herror
  filter_upwards [] with n
  obtain ⟨k, a, b, c, hrestrict, hweight⟩ := hextract n
  refine ⟨k, a, b, c, ?_, ?_⟩
  · exact TensorObj.Restrict.trans hrestrict
      (mme_kronPow_kronPow_isomorphic T r (s n)).1
  · simpa [s', pow_mul, Nat.mul_comm] using hweight
