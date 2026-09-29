-- Prove2me | solution 1 for mme_dwz_fourth_fixed_tau_value_surplus
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-09T09:36:55.665754+00:00
-- url     : https://prove2.me/submissions/08873e45-6c7a-4fee-a57a-43e65ac3a0a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_fourth_fixed_tau_value_surplus
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value

open MME
open Filter BigOperators

universe u

set_option autoImplicit false

theorem solution {K : Type u} [Field K] :
    ∃ V : ℝ, (2401 : ℝ) < V ∧
      HasSixSymmetricTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 5)
        (790643 / 1000000) V := by
  obtain ⟨V, hV, hMA⟩ :=
    mme_more_asymmetry_fourth_fixed_tau_value_surplus (K := K)
  refine ⟨V, hV, ?_⟩
  unfold MME.HasSixSymmetricTauValueAtLeast MME.HasTauValueAtLeast at hMA ⊢
  obtain ⟨hnonneg, hfreq⟩ := hMA
  refine ⟨hnonneg, ?_⟩
  intro epsilon hepsilon
  refine (hfreq epsilon hepsilon).mono ?_
  rintro N ⟨k, a, b, c, hrestrict, hbound⟩
  refine ⟨k, a, b, c, hrestrict, hbound.trans ?_⟩
  apply Finset.sum_le_sum
  intro i _
  rcases Nat.eq_zero_or_pos (a i * b i * c i) with h | h
  · have h0 : ((a i * b i * c i : ℕ) : ℝ) = 0 := by exact_mod_cast h
    rw [h0, Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num)]
  · have h1 : (1 : ℝ) ≤ ((a i * b i * c i : ℕ) : ℝ) := by
      have hh : 1 ≤ a i * b i * c i := h
      exact_mod_cast hh
    exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
