-- Prove2me | solution 1 for mme_stothers_phi233_exact_profile_product_cyclic_value_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-04T09:19:33.682377+00:00
-- url     : https://prove2.me/submissions/5d9734a6-8745-4dcd-a75b-7ea591f974cb

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_stothers_phi233_component_cyclic_value_below
import Theorems.Thm_mme_cyclic_kronFin_multiplicities_of_each_strict_below_product

open MME BigOperators
open MME.StothersFourth.Phi233

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

/-- The exact-profile Kronecker product of the ten `phi_233` components
attains every nonnegative cyclic tau-value strictly below the corresponding
endpoint product. -/
theorem solution
    {K : Type u} [Field K] (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (alpha beta gamma delta : ℕ)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V <
        ∏ r : Fin 10,
          (![MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
              MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
              MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
              MME.StothersFourth.E 6 tau ^ (2 : ℕ),
              MME.StothersFourth.L 6 tau ^ (2 : ℕ),
              MME.StothersFourth.L 6 tau ^ (2 : ℕ),
              MME.StothersFourth.E 6 tau ^ (2 : ℕ),
              MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
              MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
              MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau] :
                Fin 10 → ℝ) r ^
            profileMultiplicity alpha beta gamma delta r) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kronFin 10 (fun r ↦
          (componentObj K 6 r).kronPow
            (profileMultiplicity alpha beta gamma delta r)))) tau V := by
  let endpoint : Fin 10 → ℝ :=
    ![MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
      MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
      MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
      MME.StothersFourth.E 6 tau ^ (2 : ℕ),
      MME.StothersFourth.L 6 tau ^ (2 : ℕ),
      MME.StothersFourth.L 6 tau ^ (2 : ℕ),
      MME.StothersFourth.E 6 tau ^ (2 : ℕ),
      MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
      MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
      MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau]
  have hE : 0 < MME.StothersFourth.E 6 tau := by
    unfold MME.StothersFourth.E
    positivity
  have hH : 0 < MME.StothersFourth.H 6 tau := by
    unfold MME.StothersFourth.H
    positivity
  have hL : 0 < MME.StothersFourth.L 6 tau := by
    unfold MME.StothersFourth.L
    positivity
  have hendpoint : ∀ i, 0 < endpoint i := by
    intro i
    fin_cases i <;> dsimp [endpoint] <;> positivity
  have hlocal : ∀ (i : Fin 10) (W : ℝ),
      0 ≤ W → W < endpoint i →
      HasTauValueAtLeast
        (cyclicSymmetrization (componentObj K 6 i)) tau W := by
    intro i W hW hWlt
    exact mme_stothers_phi233_component_cyclic_value_below
      (K := K) tau htau i W hW (by simpa [endpoint] using hWlt)
  exact mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
    (fun r ↦ componentObj K 6 r)
    (profileMultiplicity alpha beta gamma delta)
    tau endpoint hendpoint hlocal V hV (by simpa [endpoint] using hVlt)
