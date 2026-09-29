-- Prove2me | solution 1 for mme_stothers_phi224_symmetric_marginal_fiber_trivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:48:02.472644+00:00
-- url     : https://prove2.me/submissions/1e930535-235a-4d8d-bd53-757aadab98a0

import Mathlib.Tactic
import Theorems.Thm_mme_stothers_phi224_marginal_fiber_parameter

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (N alpha beta gamma delta : ℕ)
    (w : MME.StothersFourth.Phi224.ProfileWord N)
    (hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ MME.StothersFourth.Phi224.modeWord w i j = s)).card =
          MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s)
    (hcomplement :
      let k : Fin 9 → ℕ := fun r ↦
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ w j = r)).card
      k 0 = k 8 ∧ k 1 = k 7 ∧ k 2 = k 6 ∧ k 3 = k 5) :
    ∀ r : Fin 9,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ w j = r)).card =
          MME.StothersFourth.Phi224.profileMultiplicity
            alpha beta gamma delta r := by
  let k : Fin 9 → ℕ := fun r ↦
    ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j ↦ w j = r)).card
  have hparameter :=
    mme_stothers_phi224_marginal_fiber_parameter
      N alpha beta gamma delta w hmarginal
  change k 0 = alpha ∧ k 8 = alpha ∧ k 4 = 2 * delta ∧
    k 1 = k 5 ∧ k 3 = k 7 ∧
    k 1 + k 3 = 2 * beta ∧
    k 1 + k 2 = beta + gamma ∧
    k 3 + k 6 = beta + gamma at hparameter
  change k 0 = k 8 ∧ k 1 = k 7 ∧ k 2 = k 6 ∧
    k 3 = k 5 at hcomplement
  rcases hparameter with
    ⟨h0, h8, h4, h15, h37, h13, h12, h36⟩
  rcases hcomplement with ⟨h08, h17, h26, h35⟩
  change ∀ r : Fin 9,
    k r =
      MME.StothersFourth.Phi224.profileMultiplicity
        alpha beta gamma delta r
  intro r
  fin_cases r <;>
    simp [MME.StothersFourth.Phi224.profileMultiplicity] at * <;>
    omega
