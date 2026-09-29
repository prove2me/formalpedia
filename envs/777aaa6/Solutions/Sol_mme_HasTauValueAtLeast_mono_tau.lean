-- Prove2me | solution 1 for mme_HasTauValueAtLeast_mono_tau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T08:54:24.083418+00:00
-- url     : https://prove2.me/submissions/c264b032-de92-44c4-b136-6c50aeb2a22e

import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {tau tau' V : ℝ}
    (htau : 0 < tau) (htau' : tau ≤ tau')
    (hV : HasTauValueAtLeast T tau V) :
    HasTauValueAtLeast T tau' V := by
  refine ⟨hV.1, ?_⟩
  intro epsilon hepsilon
  exact (hV.2 epsilon hepsilon).mono (fun N hN => by
    rcases hN with ⟨k, a, b, c, hrestrict, hweight⟩
    refine ⟨k, a, b, c, hrestrict, hweight.trans ?_⟩
    apply Finset.sum_le_sum
    intro i hi
    by_cases hzero : a i * b i * c i = 0
    · simp only [hzero, Nat.cast_zero]
      rw [Real.zero_rpow htau.ne', Real.zero_rpow (htau.trans_le htau').ne']
    · exact Real.rpow_le_rpow_of_exponent_le
        (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hzero)) htau')

