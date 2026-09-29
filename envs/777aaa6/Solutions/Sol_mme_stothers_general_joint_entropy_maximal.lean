-- Prove2me | solution 1 for mme_stothers_general_joint_entropy_maximal
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T05:54:42.028194+00:00
-- url     : https://prove2.me/submissions/e0ac62bf-77b7-4e42-a334-0357efbc47ab

import Definitions.Def_mme_stothers_general_outer_profile
import Theorems.Thm_mme_modern_entropyBits_additive_certificate

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000

namespace MME.StothersFourth

private abbrev GenJointSupportTriple :=
  {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8}

private def genJointSupportClass
    (sigma : GenJointSupportTriple) : Fin 10 :=
  if genSameOrbitExplicit sigma.1 (classRep 0) then 0 else
  if genSameOrbitExplicit sigma.1 (classRep 1) then 1 else
  if genSameOrbitExplicit sigma.1 (classRep 2) then 2 else
  if genSameOrbitExplicit sigma.1 (classRep 3) then 3 else
  if genSameOrbitExplicit sigma.1 (classRep 4) then 4 else
  if genSameOrbitExplicit sigma.1 (classRep 5) then 5 else
  if genSameOrbitExplicit sigma.1 (classRep 6) then 6 else
  if genSameOrbitExplicit sigma.1 (classRep 7) then 7 else
  if genSameOrbitExplicit sigma.1 (classRep 8) then 8 else 9

private theorem genJointSupportClass_eq_iff_explicit :
    ∀ (sigma : GenJointSupportTriple) (r : Fin 10),
      genJointSupportClass sigma = r ↔
        genSameOrbitExplicit sigma.1 (classRep r) := by
  decide

private theorem genJointSupportClass_spec
    (sigma : GenJointSupportTriple) :
    genSameOrbitExplicit sigma.1
      (classRep (genJointSupportClass sigma)) := by
  exact (genJointSupportClass_eq_iff_explicit sigma
    (genJointSupportClass sigma)).mp rfl

private theorem genJointSupportClass_fiber_card (r : Fin 10) :
    Fintype.card
        {sigma : GenJointSupportTriple // genJointSupportClass sigma = r} =
      3 * classMultiplicity r := by
  have h : ∀ r : Fin 10,
      Fintype.card
          {sigma : GenJointSupportTriple // genJointSupportClass sigma = r} =
        3 * classMultiplicity r := by
    decide
  exact h r

private noncomputable def genJointSupportDistribution
    (a : Fin 10 → ℝ) (sigma : GenJointSupportTriple) : ℝ :=
  a (genJointSupportClass sigma) / 3

private theorem genJointSupportDistribution_sum (a : Fin 10 → ℝ) :
    ∑ sigma, genJointSupportDistribution a sigma =
      ∑ r, (classMultiplicity r : ℝ) * a r := by
  rw [← Fintype.sum_fiberwise genJointSupportClass
    (genJointSupportDistribution a)]
  apply Finset.sum_congr rfl
  intro r _
  simp only [genJointSupportDistribution]
  have hconst :
      (∑ sigma :
          {sigma : GenJointSupportTriple // genJointSupportClass sigma = r},
          a (genJointSupportClass sigma.1) / 3) =
        (Fintype.card
          {sigma : GenJointSupportTriple // genJointSupportClass sigma = r} : ℝ) *
          (a r / 3) := by
    simp [show ∀ sigma :
        {sigma : GenJointSupportTriple // genJointSupportClass sigma = r},
      genJointSupportClass sigma.1 = r from fun sigma ↦ sigma.2]
  rw [hconst, genJointSupportClass_fiber_card]
  push_cast
  ring

private theorem genJointSupportDistribution_sum_eq_one
    (a : Fin 10 → ℝ) (ha : InZ a) :
    ∑ sigma, genJointSupportDistribution a sigma = 1 := by
  rw [genJointSupportDistribution_sum]
  exact ha.2

private theorem genJointSupportDistribution_pos
    (a : Fin 10 → ℝ) (ha : ∀ r, 0 < a r) :
    ∀ sigma, 0 < genJointSupportDistribution a sigma := by
  intro sigma
  exact div_pos (ha _) (by norm_num)

private noncomputable def genJointSupportClassLog
    (b : Fin 10 → ℝ) (r : Fin 10) : ℝ :=
  Real.log (b r) / Real.log 2

private noncomputable def genJointPotential4 (b : Fin 10 → ℝ) : ℝ :=
  genJointSupportClassLog b 4 / 2

private noncomputable def genJointPotential2 (b : Fin 10 → ℝ) : ℝ :=
  (genJointSupportClassLog b 8 - genJointPotential4 b) / 2

private noncomputable def genJointPotential3 (b : Fin 10 → ℝ) : ℝ :=
  (genJointSupportClassLog b 9 - genJointPotential2 b) / 2

private noncomputable def genJointPotential1 (b : Fin 10 → ℝ) : ℝ :=
  genJointSupportClassLog b 7 - genJointPotential3 b -
    genJointPotential4 b

private noncomputable def genJointPotential6 (b : Fin 10 → ℝ) : ℝ :=
  genJointSupportClassLog b 5 - 2 * genJointPotential1 b

private noncomputable def genJointPotential5 (b : Fin 10 → ℝ) : ℝ :=
  genJointSupportClassLog b 6 - genJointPotential1 b -
    genJointPotential2 b

private noncomputable def genJointPotential7 (b : Fin 10 → ℝ) : ℝ :=
  genJointSupportClassLog b 1 - genJointPotential1 b

private noncomputable def genJointSupportEntropyPotential
    (b : Fin 10 → ℝ) : Fin 9 → ℝ :=
  ![0, genJointPotential1 b, genJointPotential2 b,
    genJointPotential3 b, genJointPotential4 b,
    genJointPotential5 b, genJointPotential6 b,
    genJointPotential7 b, genJointSupportClassLog b 0]

private theorem genJointSupportClassLog_relations
    (b : Fin 10 → ℝ) (hb : InN b) (hbpos : ∀ r, 0 < b r) :
    genJointSupportClassLog b 2 + 2 * genJointSupportClassLog b 7 =
        genJointSupportClassLog b 4 + genJointSupportClassLog b 5 +
          genJointSupportClassLog b 9 ∧
      genJointSupportClassLog b 3 + genJointSupportClassLog b 7 +
          genJointSupportClassLog b 8 =
        genJointSupportClassLog b 4 + genJointSupportClassLog b 6 +
          genJointSupportClassLog b 9 := by
  rcases hb with ⟨_, hmul1, hmul2⟩
  have hlog1 := congrArg Real.log hmul1
  have hlog2 := congrArg Real.log hmul2
  rw [Real.log_mul (ne_of_gt (hbpos 2))
      (pow_ne_zero 2 (ne_of_gt (hbpos 7))),
    Real.log_pow,
    Real.log_mul (mul_ne_zero (ne_of_gt (hbpos 4)) (ne_of_gt (hbpos 5)))
      (ne_of_gt (hbpos 9)),
    Real.log_mul (ne_of_gt (hbpos 4)) (ne_of_gt (hbpos 5))] at hlog1
  rw [Real.log_mul (mul_ne_zero (ne_of_gt (hbpos 3)) (ne_of_gt (hbpos 7)))
      (ne_of_gt (hbpos 8)),
    Real.log_mul (ne_of_gt (hbpos 3)) (ne_of_gt (hbpos 7)),
    Real.log_mul (mul_ne_zero (ne_of_gt (hbpos 4)) (ne_of_gt (hbpos 6)))
      (ne_of_gt (hbpos 9)),
    Real.log_mul (ne_of_gt (hbpos 4)) (ne_of_gt (hbpos 6))] at hlog2
  norm_num at hlog1 hlog2
  constructor
  · change Real.log (b 2) / Real.log 2 +
        2 * (Real.log (b 7) / Real.log 2) =
      Real.log (b 4) / Real.log 2 + Real.log (b 5) / Real.log 2 +
        Real.log (b 9) / Real.log 2
    calc
      Real.log (b 2) / Real.log 2 +
          2 * (Real.log (b 7) / Real.log 2) =
          (Real.log (b 2) + 2 * Real.log (b 7)) / Real.log 2 := by ring
      _ = (Real.log (b 4) + Real.log (b 5) + Real.log (b 9)) /
          Real.log 2 := by rw [hlog1]
      _ = Real.log (b 4) / Real.log 2 + Real.log (b 5) / Real.log 2 +
          Real.log (b 9) / Real.log 2 := by ring
  · change Real.log (b 3) / Real.log 2 + Real.log (b 7) / Real.log 2 +
        Real.log (b 8) / Real.log 2 =
      Real.log (b 4) / Real.log 2 + Real.log (b 6) / Real.log 2 +
        Real.log (b 9) / Real.log 2
    calc
      Real.log (b 3) / Real.log 2 + Real.log (b 7) / Real.log 2 +
          Real.log (b 8) / Real.log 2 =
          (Real.log (b 3) + Real.log (b 7) + Real.log (b 8)) /
            Real.log 2 := by ring
      _ = (Real.log (b 4) + Real.log (b 6) + Real.log (b 9)) /
          Real.log 2 := by rw [hlog2]
      _ = Real.log (b 4) / Real.log 2 + Real.log (b 6) / Real.log 2 +
          Real.log (b 9) / Real.log 2 := by ring

private theorem genJointSupportEntropyPotential_on_classRep
    (b : Fin 10 → ℝ) (hb : InN b) (hbpos : ∀ r, 0 < b r) :
    ∀ r,
      genJointSupportEntropyPotential b (classRep r 0) +
          genJointSupportEntropyPotential b (classRep r 1) +
          genJointSupportEntropyPotential b (classRep r 2) =
        genJointSupportClassLog b r := by
  rcases genJointSupportClassLog_relations b hb hbpos with ⟨hrel1, hrel2⟩
  intro r
  fin_cases r <;>
    simp [genJointSupportEntropyPotential, genJointPotential1,
      genJointPotential2, genJointPotential3, genJointPotential4,
      genJointPotential5, genJointPotential6, genJointPotential7,
      classRep, cwFourthBlockType] <;>
    linarith

private theorem genJointSupportEntropyPotential_sum_eq_rep
    (b : Fin 10 → ℝ) (sigma : GenJointSupportTriple) :
    genJointSupportEntropyPotential b (sigma.1 0) +
        genJointSupportEntropyPotential b (sigma.1 1) +
        genJointSupportEntropyPotential b (sigma.1 2) =
      genJointSupportEntropyPotential b
          (classRep (genJointSupportClass sigma) 0) +
        genJointSupportEntropyPotential b
          (classRep (genJointSupportClass sigma) 1) +
        genJointSupportEntropyPotential b
          (classRep (genJointSupportClass sigma) 2) := by
  have h := genJointSupportClass_spec sigma
  rcases h with h | h | h | h | h | h <;>
    rcases h with ⟨h0, h1, h2⟩ <;>
    simp only [h0, h1, h2] <;> ring

private theorem genJointSupportDistribution_exact_additive_potential
    (b : Fin 10 → ℝ) (hb : InN b) (hbpos : ∀ r, 0 < b r)
    (sigma : GenJointSupportTriple) :
    Real.log (genJointSupportDistribution b sigma) / Real.log 2 =
      (-Real.log 3 / Real.log 2) +
        genJointSupportEntropyPotential b (sigma.1 0) +
        genJointSupportEntropyPotential b (sigma.1 1) +
        genJointSupportEntropyPotential b (sigma.1 2) := by
  let r := genJointSupportClass sigma
  have hrep := genJointSupportEntropyPotential_on_classRep b hb hbpos r
  have hsum := genJointSupportEntropyPotential_sum_eq_rep b sigma
  calc
    Real.log (genJointSupportDistribution b sigma) / Real.log 2 =
        -Real.log 3 / Real.log 2 + genJointSupportClassLog b r := by
      change Real.log (b r / 3) / Real.log 2 =
        -Real.log 3 / Real.log 2 + Real.log (b r) / Real.log 2
      rw [Real.log_div (ne_of_gt (hbpos r))
        (by norm_num : (3 : ℝ) ≠ 0)]
      ring
    _ = -Real.log 3 / Real.log 2 +
        (genJointSupportEntropyPotential b (classRep r 0) +
          genJointSupportEntropyPotential b (classRep r 1) +
          genJointSupportEntropyPotential b (classRep r 2)) := by
      rw [hrep]
    _ = (-Real.log 3 / Real.log 2) +
        genJointSupportEntropyPotential b (sigma.1 0) +
        genJointSupportEntropyPotential b (sigma.1 1) +
        genJointSupportEntropyPotential b (sigma.1 2) := by
      linarith [hsum]

private theorem genJointTarget_eq_distribution (bstar : Fin 10 → ℕ)
    (sigma : GenJointSupportTriple) :
    (genJointMultiplicity bstar 1 sigma.1 : ℝ) /
        (genOuterLength bstar 1 : ℝ) =
      genJointSupportDistribution (genProfileB bstar) sigma := by
  have horbit : genSameOrbitExplicit sigma.1
      (classRep (genJointSupportClass sigma)) :=
    genJointSupportClass_spec sigma
  have hunique : ∀ r : Fin 10,
      genSameOrbitExplicit sigma.1 (classRep r) ↔
        r = genJointSupportClass sigma := by
    intro r
    constructor
    · intro hr
      exact ((genJointSupportClass_eq_iff_explicit sigma r).mpr hr).symm
    · intro hr
      simpa [hr] using horbit
  simp only [genJointMultiplicity, genProfileCount]
  rw [show (∑ r : Fin 10,
      if genSameOrbitExplicit sigma.1 (classRep r) then
        bstar r * 1 else 0) =
      bstar (genJointSupportClass sigma) by
    classical
    rw [Finset.sum_eq_single (genJointSupportClass sigma)]
    · simp [hunique]
    · intro r _ hr
      simp [hunique, hr]
    · simp]
  simp only [genJointSupportDistribution, genProfileB, genOuterLength]
  push_cast
  ring

theorem mme_stothers_general_joint_entropy_maximal
    (bstar : Fin 10 → ℕ) (hpos : ∀ r, 0 < bstar r)
    (hInN : InN (genProfileB bstar)) :
    let Omega :=
      {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8}
    let target : Omega → ℝ := fun sigma ↦
      (genJointMultiplicity bstar 1 sigma.1 : ℝ) /
        (genOuterLength bstar 1 : ℝ)
    ∀ rho : Omega → ℝ,
      (∀ sigma, 0 ≤ rho sigma) →
      (∑ sigma, rho sigma) = 1 →
      (∀ s : Fin 3, ∀ j : Fin 9,
        mme_modern_marginal (fun sigma : Omega ↦ sigma.1 s) rho j =
          mme_modern_marginal
            (fun sigma : Omega ↦ sigma.1 s) target j) →
      mme_modern_entropyBits rho ≤ mme_modern_entropyBits target := by
  dsimp only
  have hBpos : ∀ r : Fin 10, 0 < genProfileB bstar r := by
    intro r
    have hs : 0 < genProfileScale bstar := by
      refine Finset.sum_pos' (fun i _ ↦ Nat.zero_le _)
        ⟨0, Finset.mem_univ 0, ?_⟩
      have h0 := hpos 0
      simpa [classMultiplicity] using h0
    have h1 : (0 : ℝ) < (bstar r : ℝ) := by exact_mod_cast hpos r
    have h2 : (0 : ℝ) < (genProfileScale bstar : ℝ) := by exact_mod_cast hs
    exact div_pos h1 h2
  let target : GenJointSupportTriple → ℝ := fun sigma ↦
    (genJointMultiplicity bstar 1 sigma.1 : ℝ) /
      (genOuterLength bstar 1 : ℝ)
  have htarget : target =
      genJointSupportDistribution (genProfileB bstar) := by
    funext sigma
    exact genJointTarget_eq_distribution bstar sigma
  intro rho hrho hsum hmarginal
  change (∀ s : Fin 3, ∀ j : Fin 9,
      mme_modern_marginal
          (fun sigma : GenJointSupportTriple ↦ sigma.1 s) rho j =
        mme_modern_marginal
          (fun sigma : GenJointSupportTriple ↦ sigma.1 s) target j)
    at hmarginal
  change mme_modern_entropyBits rho ≤ mme_modern_entropyBits target
  rw [htarget] at hmarginal ⊢
  have hmax :
      mme_modern_entropyBits rho ≤
        mme_modern_entropyBits
            (genJointSupportDistribution (genProfileB bstar)) + 2 * 0 := by
    apply mme_modern_entropyBits_additive_certificate
      (fun sigma : GenJointSupportTriple ↦ sigma.1 0)
      (fun sigma : GenJointSupportTriple ↦ sigma.1 1)
      (fun sigma : GenJointSupportTriple ↦ sigma.1 2)
      rho (genJointSupportDistribution (genProfileB bstar))
      (-Real.log 3 / Real.log 2)
      (genJointSupportEntropyPotential (genProfileB bstar))
      (genJointSupportEntropyPotential (genProfileB bstar))
      (genJointSupportEntropyPotential (genProfileB bstar)) 0
    · exact hrho
    · exact genJointSupportDistribution_pos (genProfileB bstar) hBpos
    · exact hsum
    · exact genJointSupportDistribution_sum_eq_one (genProfileB bstar) hInN.1
    · exact hmarginal 0
    · exact hmarginal 1
    · exact hmarginal 2
    · norm_num
    · intro sigma
      rw [genJointSupportDistribution_exact_additive_potential
        (genProfileB bstar) hInN hBpos sigma]
      norm_num
  simpa using hmax

end MME.StothersFourth

theorem solution
    (bstar : Fin 10 → ℕ) (hpos : ∀ r, 0 < bstar r)
    (hInN : MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar)) :
    let Omega :=
      {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8}
    let target : Omega → ℝ := fun sigma ↦
      (MME.StothersFourth.genJointMultiplicity bstar 1 sigma.1 : ℝ) /
        (MME.StothersFourth.genOuterLength bstar 1 : ℝ)
    ∀ rho : Omega → ℝ,
      (∀ sigma, 0 ≤ rho sigma) →
      (∑ sigma, rho sigma) = 1 →
      (∀ s : Fin 3, ∀ j : Fin 9,
        mme_modern_marginal (fun sigma : Omega ↦ sigma.1 s) rho j =
          mme_modern_marginal
            (fun sigma : Omega ↦ sigma.1 s) target j) →
      mme_modern_entropyBits rho ≤ mme_modern_entropyBits target :=
  MME.StothersFourth.mme_stothers_general_joint_entropy_maximal bstar hpos hInN
