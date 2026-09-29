-- Prove2me | solution 1 for mme_stothers_phi224_marginal_orbit_averages
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:37:32.71315+00:00
-- url     : https://prove2.me/submissions/bee41d33-395d-43b6-bad1-014ad0d28ba3

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (alpha beta gamma delta : ℕ) (x : Fin 9 → ℝ)
    (hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      (∑ r : Fin 9,
        if MME.StothersFourth.Phi224.pattern r i = s then x r else 0) =
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s : ℝ)) :
    (x 0 + x 8) / 2 = alpha ∧
      (x 1 + x 3 + x 5 + x 7) / 4 = beta ∧
      (x 2 + x 6) / 2 = gamma ∧
      x 4 = 2 * delta := by
  have h00 := hmarginal 0 0
  have h01 := hmarginal 0 1
  have h02 := hmarginal 0 2
  have h10 := hmarginal 1 0
  have h11 := hmarginal 1 1
  have h12 := hmarginal 1 2
  have h20 := hmarginal 2 0
  have h21 := hmarginal 2 1
  have h23 := hmarginal 2 3
  have h24 := hmarginal 2 4
  simp [MME.StothersFourth.Phi224.pattern,
    MME.StothersFourth.Phi224.marginalMultiplicity,
    Fin.sum_univ_succ] at h00 h01 h02 h10 h11 h12 h20 h21 h23 h24
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith
