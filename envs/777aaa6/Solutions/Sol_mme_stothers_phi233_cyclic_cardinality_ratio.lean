-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_cardinality_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:19:37.855277+00:00
-- url     : https://prove2.me/submissions/ce42f5f8-e7ba-474f-9d61-5f7d81de52a1

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
import Theorems.Thm_mme_stothers_phi233_cyclic_finset_cardinalities

open MME

set_option autoImplicit false
set_option warningAsError true

/-- A one-coordinate completion ratio cubes exactly after cyclic
symmetrization.  This is the cardinality interface between the `phi_233`
entropy estimate and a three-mode hashing/pruning argument. -/
theorem solution
    (N alpha beta gamma delta : ℕ) (R : ℝ)
    (hratio :
      (Nat.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta) : ℝ) ≤
        R *
          (Nat.card
            (MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta) : ℝ)) :
    ((MME.StothersFourth.Phi233.ambientFinset
        N alpha beta gamma delta).card : ℝ) ≤
      R ^ 3 *
        ((MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta).card : ℝ) := by
  obtain ⟨_, htargetCard, hambientCard⟩ :=
    mme_stothers_phi233_cyclic_finset_cardinalities
      N alpha beta gamma delta
  have hpow := pow_le_pow_left₀
    (Nat.cast_nonneg
      (Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta))) hratio 3
  rw [hambientCard, htargetCard]
  push_cast
  calc
    (Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta) : ℝ) ^ 3 ≤
        (R *
          (Nat.card
            (MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta) : ℝ)) ^ 3 := hpow
    _ = R ^ 3 *
        (Nat.card
          (MME.StothersFourth.Phi233.ExactProfileAddress
            N alpha beta gamma delta) : ℝ) ^ 3 := by ring
