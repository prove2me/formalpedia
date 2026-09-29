-- Prove2me | solution 1 for mme_stothers_phi134_cyclic_cofinal_finite_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:40:55.144403+00:00
-- url     : https://prove2.me/submissions/2f935748-605a-4cee-9c5d-0b90b14f9fa8

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Theorems.Thm_mme_stothers_phi134_profile_cofinal_finite_extraction
import Theorems.Thm_mme_stothers_q6_EHL_optimizer_regime
import Theorems.Thm_mme_stothers_remaining_four_optimizer_certificates

open MME BigOperators Filter

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (tau : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < MME.StothersFourth.classValue 6 tau 7) :
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (x y z : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (x i) (y i) (z i)))
            ((cyclicSymmetrization
              (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)).kronPow
                (s n)) ∧
          V ^ (s n) * (1 - loss n) ≤
            ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by
  let E := MME.StothersFourth.E 6 tau
  let H := MME.StothersFourth.H 6 tau
  let L := MME.StothersFourth.L 6 tau
  let sigma := L / (E + L)
  let a := 2 / (2 + 2 * E + H)
  let c := H / (2 + 2 * E + H)
  obtain ⟨h16E, hEH, hHL, hL4H, h224left, h224right⟩ :=
    mme_stothers_q6_EHL_optimizer_regime tau htauLower htauUpper
  have hopt :=
    mme_stothers_remaining_four_optimizer_certificates
      E H L h16E hEH hHL hL4H h224left h224right
  change
    _ ∧
      (0 < a ∧ 0 < c ∧ c ≤ sigma ∧ sigma + a ≤ 1 ∧
        8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c)) =
          4 * (E + L) * (2 + 2 * E + H)) ∧ _ at hopt
  rcases hopt.2.1 with ⟨ha, hc, hcs, hsa, hrate⟩
  apply mme_stothers_phi134_profile_cofinal_finite_extraction
    tau sigma a c htauLower htauUpper ha hc hcs hsa V hV
  calc
    V < MME.StothersFourth.classValue 6 tau 7 := hVlt
    _ = 4 * (E + L) * (2 + 2 * E + H) := rfl
    _ = 8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c)) := hrate.symm
