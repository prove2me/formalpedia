-- Prove2me | solution 1 for mme_stothers_phi224_normalized_same_marginal_entropy_maximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:15:16.563509+00:00
-- url     : https://prove2.me/submissions/203549b1-9eb6-45a6-a745-a07603af1a85

import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_stothers_phi224_normalized_marginal_orbit_averages
import Theorems.Thm_mme_stothers_phi224_orbit_entropy_symmetrization

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (x : Fin 9 → ℝ) (hx : ∀ r, 0 ≤ x r)
    (hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      (∑ r : Fin 9,
        if MME.StothersFourth.Phi224.pattern r i = s then x r else 0) =
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s : ℝ) / ((2 * N : ℕ) : ℝ)) :
    (∑ r : Fin 9, Real.negMulLog (x r)) ≤
      2 * Real.negMulLog
        ((alpha : ℝ) / ((2 * N : ℕ) : ℝ)) +
      4 * Real.negMulLog
        ((beta : ℝ) / ((2 * N : ℕ) : ℝ)) +
      2 * Real.negMulLog
        ((gamma : ℝ) / ((2 * N : ℕ) : ℝ)) +
      Real.negMulLog
        (((2 * delta : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)) := by
  have horbit :=
    mme_stothers_phi224_orbit_entropy_symmetrization x hx
  obtain ⟨ha, hb, hc, hd⟩ :=
    mme_stothers_phi224_normalized_marginal_orbit_averages
      N alpha beta gamma delta hN x hmarginal
  rw [ha, hb, hc, hd] at horbit
  exact horbit
