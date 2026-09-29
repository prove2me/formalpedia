-- Prove2me | solution 1 for mme_stothers_phi125_cyclic_cofinal_finite_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:03:30.904984+00:00
-- url     : https://prove2.me/submissions/405c6bec-7cf0-4c6f-80a9-ca10c3d86cc0

import Theorems.Thm_mme_stothers_phi125_profile_cofinal_finite_extraction
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
    (hVlt : V < MME.StothersFourth.classValue 6 tau 6) :
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization
              (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)).kronPow
                (s n)) ∧
          V ^ (s n) * (1 - loss n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  let E := MME.StothersFourth.E 6 tau
  let H := MME.StothersFourth.H 6 tau
  let L := MME.StothersFourth.L 6 tau
  let a := L / (L + E * H)
  let b := L / (L + 2 * H)
  obtain ⟨h16E, hEH, hHL, hL4H, h224left, h224right⟩ :=
    mme_stothers_q6_EHL_optimizer_regime tau htauLower htauUpper
  have hopt :=
    mme_stothers_remaining_four_optimizer_certificates
      E H L h16E hEH hHL hL4H h224left h224right
  change
    (0 < a ∧ 0 < b ∧ a + b ≤ 1 ∧
      4 / H *
          ((L / a) ^ a * ((E * H) / (1 - a)) ^ (1 - a)) *
          ((L / b) ^ b * ((2 * H) / (1 - b)) ^ (1 - b)) =
        4 * (L + E * H) * (2 * H + L) / H) ∧ _ at hopt
  rcases hopt.1 with ⟨ha, hb, hab, hrate⟩
  apply mme_stothers_phi125_profile_cofinal_finite_extraction
    tau a b htauLower htauUpper ha hb hab V hV
  calc
    V < MME.StothersFourth.classValue 6 tau 6 := hVlt
    _ = 4 * (L + E * H) * (2 * H + L) / H := rfl
    _ = 4 / H *
          ((L / a) ^ a * ((E * H) / (1 - a)) ^ (1 - a)) *
          ((L / b) ^ b * ((2 * H) / (1 - b)) ^ (1 - b)) := hrate.symm
