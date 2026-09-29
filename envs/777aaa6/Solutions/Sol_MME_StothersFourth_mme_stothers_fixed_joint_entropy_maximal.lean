-- Prove2me | solution 1 for MME.StothersFourth.mme_stothers_fixed_joint_entropy_maximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T19:30:51.140179+00:00
-- url     : https://prove2.me/submissions/c28ca843-d312-475d-ab88-fac80579a0d0

import Definitions.Def_mme_stothers_fixed_outer_profile
import Theorems.Thm_mme_modern_entropyBits_additive_certificate

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000

namespace MME.StothersFourth

/-!
This file is intentionally self-contained at the platform boundary.  All
auxiliary declarations are private, so publishing the theorem does not reserve
generic names such as `SupportTriple` or `supportClass`.
-/

private abbrev FixedHashSupportTriple :=
  {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8}

private def fixedHashSupportClass
    (sigma : FixedHashSupportTriple) : Fin 10 :=
  if fixedSameOrbitExplicit sigma.1 (classRep 0) then 0 else
  if fixedSameOrbitExplicit sigma.1 (classRep 1) then 1 else
  if fixedSameOrbitExplicit sigma.1 (classRep 2) then 2 else
  if fixedSameOrbitExplicit sigma.1 (classRep 3) then 3 else
  if fixedSameOrbitExplicit sigma.1 (classRep 4) then 4 else
  if fixedSameOrbitExplicit sigma.1 (classRep 5) then 5 else
  if fixedSameOrbitExplicit sigma.1 (classRep 6) then 6 else
  if fixedSameOrbitExplicit sigma.1 (classRep 7) then 7 else
  if fixedSameOrbitExplicit sigma.1 (classRep 8) then 8 else 9

private theorem fixedHashSupportClass_eq_iff_explicit :
    ∀ (sigma : FixedHashSupportTriple) (r : Fin 10),
      fixedHashSupportClass sigma = r ↔
        fixedSameOrbitExplicit sigma.1 (classRep r) := by
  decide

private theorem fixedHashSupportClass_spec
    (sigma : FixedHashSupportTriple) :
    fixedSameOrbitExplicit sigma.1
      (classRep (fixedHashSupportClass sigma)) := by
  exact (fixedHashSupportClass_eq_iff_explicit sigma
    (fixedHashSupportClass sigma)).mp rfl

private theorem fixedHashSupportClass_fiber_card (r : Fin 10) :
    Fintype.card
        {sigma : FixedHashSupportTriple // fixedHashSupportClass sigma = r} =
      3 * classMultiplicity r := by
  have h : ∀ r : Fin 10,
      Fintype.card
          {sigma : FixedHashSupportTriple // fixedHashSupportClass sigma = r} =
        3 * classMultiplicity r := by
    decide
  exact h r

private noncomputable def fixedHashSupportDistribution
    (a : Fin 10 → ℝ) (sigma : FixedHashSupportTriple) : ℝ :=
  a (fixedHashSupportClass sigma) / 3

private theorem fixedHashSupportDistribution_sum (a : Fin 10 → ℝ) :
    ∑ sigma, fixedHashSupportDistribution a sigma =
      ∑ r, (classMultiplicity r : ℝ) * a r := by
  rw [← Fintype.sum_fiberwise fixedHashSupportClass
    (fixedHashSupportDistribution a)]
  apply Finset.sum_congr rfl
  intro r _
  simp only [fixedHashSupportDistribution]
  have hconst :
      (∑ sigma :
          {sigma : FixedHashSupportTriple // fixedHashSupportClass sigma = r},
          a (fixedHashSupportClass sigma.1) / 3) =
        (Fintype.card
          {sigma : FixedHashSupportTriple // fixedHashSupportClass sigma = r} : ℝ) *
          (a r / 3) := by
    simp [show ∀ sigma :
        {sigma : FixedHashSupportTriple // fixedHashSupportClass sigma = r},
      fixedHashSupportClass sigma.1 = r from fun sigma ↦ sigma.2]
  rw [hconst, fixedHashSupportClass_fiber_card]
  push_cast
  ring

private theorem fixedHashSupportDistribution_sum_eq_one
    (a : Fin 10 → ℝ) (ha : InZ a) :
    ∑ sigma, fixedHashSupportDistribution a sigma = 1 := by
  rw [fixedHashSupportDistribution_sum]
  exact ha.2

private theorem fixedHashSupportDistribution_pos
    (a : Fin 10 → ℝ) (ha : ∀ r, 0 < a r) :
    ∀ sigma, 0 < fixedHashSupportDistribution a sigma := by
  intro sigma
  exact div_pos (ha _) (by norm_num)

private noncomputable def fixedHashSupportClassLog
    (b : Fin 10 → ℝ) (r : Fin 10) : ℝ :=
  Real.log (b r) / Real.log 2

private noncomputable def fixedHashPotential4 (b : Fin 10 → ℝ) : ℝ :=
  fixedHashSupportClassLog b 4 / 2

private noncomputable def fixedHashPotential2 (b : Fin 10 → ℝ) : ℝ :=
  (fixedHashSupportClassLog b 8 - fixedHashPotential4 b) / 2

private noncomputable def fixedHashPotential3 (b : Fin 10 → ℝ) : ℝ :=
  (fixedHashSupportClassLog b 9 - fixedHashPotential2 b) / 2

private noncomputable def fixedHashPotential1 (b : Fin 10 → ℝ) : ℝ :=
  fixedHashSupportClassLog b 7 - fixedHashPotential3 b -
    fixedHashPotential4 b

private noncomputable def fixedHashPotential6 (b : Fin 10 → ℝ) : ℝ :=
  fixedHashSupportClassLog b 5 - 2 * fixedHashPotential1 b

private noncomputable def fixedHashPotential5 (b : Fin 10 → ℝ) : ℝ :=
  fixedHashSupportClassLog b 6 - fixedHashPotential1 b -
    fixedHashPotential2 b

private noncomputable def fixedHashPotential7 (b : Fin 10 → ℝ) : ℝ :=
  fixedHashSupportClassLog b 1 - fixedHashPotential1 b

private noncomputable def fixedHashSupportEntropyPotential
    (b : Fin 10 → ℝ) : Fin 9 → ℝ :=
  ![0, fixedHashPotential1 b, fixedHashPotential2 b,
    fixedHashPotential3 b, fixedHashPotential4 b,
    fixedHashPotential5 b, fixedHashPotential6 b,
    fixedHashPotential7 b, fixedHashSupportClassLog b 0]

private theorem fixedHashSupportClassLog_relations
    (b : Fin 10 → ℝ) (hb : InN b) (hbpos : ∀ r, 0 < b r) :
    fixedHashSupportClassLog b 2 + 2 * fixedHashSupportClassLog b 7 =
        fixedHashSupportClassLog b 4 + fixedHashSupportClassLog b 5 +
          fixedHashSupportClassLog b 9 ∧
      fixedHashSupportClassLog b 3 + fixedHashSupportClassLog b 7 +
          fixedHashSupportClassLog b 8 =
        fixedHashSupportClassLog b 4 + fixedHashSupportClassLog b 6 +
          fixedHashSupportClassLog b 9 := by
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

private theorem fixedHashSupportEntropyPotential_on_classRep
    (b : Fin 10 → ℝ) (hb : InN b) (hbpos : ∀ r, 0 < b r) :
    ∀ r,
      fixedHashSupportEntropyPotential b (classRep r 0) +
          fixedHashSupportEntropyPotential b (classRep r 1) +
          fixedHashSupportEntropyPotential b (classRep r 2) =
        fixedHashSupportClassLog b r := by
  rcases fixedHashSupportClassLog_relations b hb hbpos with ⟨hrel1, hrel2⟩
  intro r
  fin_cases r <;>
    simp [fixedHashSupportEntropyPotential, fixedHashPotential1,
      fixedHashPotential2, fixedHashPotential3, fixedHashPotential4,
      fixedHashPotential5, fixedHashPotential6, fixedHashPotential7,
      classRep, cwFourthBlockType] <;>
    linarith

private theorem fixedHashSupportEntropyPotential_sum_eq_rep
    (b : Fin 10 → ℝ) (sigma : FixedHashSupportTriple) :
    fixedHashSupportEntropyPotential b (sigma.1 0) +
        fixedHashSupportEntropyPotential b (sigma.1 1) +
        fixedHashSupportEntropyPotential b (sigma.1 2) =
      fixedHashSupportEntropyPotential b
          (classRep (fixedHashSupportClass sigma) 0) +
        fixedHashSupportEntropyPotential b
          (classRep (fixedHashSupportClass sigma) 1) +
        fixedHashSupportEntropyPotential b
          (classRep (fixedHashSupportClass sigma) 2) := by
  have h := fixedHashSupportClass_spec sigma
  rcases h with h | h | h | h | h | h <;>
    rcases h with ⟨h0, h1, h2⟩ <;>
    simp only [h0, h1, h2] <;> ring

private theorem fixedHashSupportDistribution_exact_additive_potential
    (b : Fin 10 → ℝ) (hb : InN b) (hbpos : ∀ r, 0 < b r)
    (sigma : FixedHashSupportTriple) :
    Real.log (fixedHashSupportDistribution b sigma) / Real.log 2 =
      (-Real.log 3 / Real.log 2) +
        fixedHashSupportEntropyPotential b (sigma.1 0) +
        fixedHashSupportEntropyPotential b (sigma.1 1) +
        fixedHashSupportEntropyPotential b (sigma.1 2) := by
  let r := fixedHashSupportClass sigma
  have hrep := fixedHashSupportEntropyPotential_on_classRep b hb hbpos r
  have hsum := fixedHashSupportEntropyPotential_sum_eq_rep b sigma
  calc
    Real.log (fixedHashSupportDistribution b sigma) / Real.log 2 =
        -Real.log 3 / Real.log 2 + fixedHashSupportClassLog b r := by
      change Real.log (b r / 3) / Real.log 2 =
        -Real.log 3 / Real.log 2 + Real.log (b r) / Real.log 2
      rw [Real.log_div (ne_of_gt (hbpos r))
        (by norm_num : (3 : ℝ) ≠ 0)]
      ring
    _ = -Real.log 3 / Real.log 2 +
        (fixedHashSupportEntropyPotential b (classRep r 0) +
          fixedHashSupportEntropyPotential b (classRep r 1) +
          fixedHashSupportEntropyPotential b (classRep r 2)) := by
      rw [hrep]
    _ = (-Real.log 3 / Real.log 2) +
        fixedHashSupportEntropyPotential b (sigma.1 0) +
        fixedHashSupportEntropyPotential b (sigma.1 1) +
        fixedHashSupportEntropyPotential b (sigma.1 2) := by
      linarith [hsum]

private theorem fixedHashProfileB_pos :
    ∀ r : Fin 10, 0 < fixedProfileB r := by
  intro r
  fin_cases r <;>
    norm_num [fixedProfileB, fixedProfileBaseCount, fixedProfileScale]

private theorem fixedHashProfileB_InN : InN fixedProfileB := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · exact fun r ↦ (fixedHashProfileB_pos r).le
    · norm_num [fixedProfileB, fixedProfileBaseCount, fixedProfileScale,
        classMultiplicity, Fin.sum_univ_succ]
      rfl
  · change
      ((73075 : ℝ) / 97942072) *
          ((13720000 : ℝ) / 97942072) ^ (2 : ℕ) =
        ((3626000 : ℝ) / 97942072) *
          ((98000 : ℝ) / 97942072) *
            ((38710000 : ℝ) / 97942072)
    norm_num
  · change
      ((1023050 : ℝ) / 97942072) *
          ((13720000 : ℝ) / 97942072) *
            ((21560000 : ℝ) / 97942072) =
        ((3626000 : ℝ) / 97942072) *
          ((2156000 : ℝ) / 97942072) *
            ((38710000 : ℝ) / 97942072)
    norm_num

private theorem fixedHashTarget_eq_distribution
    (sigma : FixedHashSupportTriple) :
    (fixedJointMultiplicity 1 sigma.1 : ℝ) /
        (fixedOuterLength 1 : ℝ) =
      fixedHashSupportDistribution fixedProfileB sigma := by
  have horbit : fixedSameOrbitExplicit sigma.1
      (classRep (fixedHashSupportClass sigma)) :=
    fixedHashSupportClass_spec sigma
  have hunique : ∀ r : Fin 10,
      fixedSameOrbitExplicit sigma.1 (classRep r) ↔
        r = fixedHashSupportClass sigma := by
    intro r
    constructor
    · intro hr
      exact ((fixedHashSupportClass_eq_iff_explicit sigma r).mpr hr).symm
    · intro hr
      simpa [hr] using horbit
  simp only [fixedJointMultiplicity, fixedProfileCount]
  rw [show (∑ r : Fin 10,
      if fixedSameOrbitExplicit sigma.1 (classRep r) then
        1 * fixedProfileBaseCount r else 0) =
      fixedProfileBaseCount (fixedHashSupportClass sigma) by
    classical
    rw [Finset.sum_eq_single (fixedHashSupportClass sigma)]
    · simp [hunique]
    · intro r _ hr
      simp [hunique, hr]
    · simp]
  unfold fixedHashSupportDistribution fixedProfileB
  norm_num [fixedOuterLength, fixedProfileScale]
  ring

/-- The fixed stationary 45-cell distribution maximizes Shannon entropy
among every ordered supported distribution with the same three marginals.
No permutation-symmetry hypothesis is imposed on the competitor. -/
theorem mme_stothers_fixed_joint_entropy_maximal :
    let Omega :=
      {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8}
    let target : Omega → ℝ := fun sigma ↦
      (fixedJointMultiplicity 1 sigma.1 : ℝ) /
        (fixedOuterLength 1 : ℝ)
    ∀ rho : Omega → ℝ,
      (∀ sigma, 0 ≤ rho sigma) →
      (∑ sigma, rho sigma) = 1 →
      (∀ s : Fin 3, ∀ j : Fin 9,
        mme_modern_marginal (fun sigma : Omega ↦ sigma.1 s) rho j =
          mme_modern_marginal
            (fun sigma : Omega ↦ sigma.1 s) target j) →
      mme_modern_entropyBits rho ≤ mme_modern_entropyBits target := by
  dsimp only
  let target : FixedHashSupportTriple → ℝ := fun sigma ↦
    (fixedJointMultiplicity 1 sigma.1 : ℝ) /
      (fixedOuterLength 1 : ℝ)
  have htarget : target =
      fixedHashSupportDistribution fixedProfileB := by
    funext sigma
    exact fixedHashTarget_eq_distribution sigma
  intro rho hrho hsum hmarginal
  change (∀ s : Fin 3, ∀ j : Fin 9,
      mme_modern_marginal
          (fun sigma : FixedHashSupportTriple ↦ sigma.1 s) rho j =
        mme_modern_marginal
          (fun sigma : FixedHashSupportTriple ↦ sigma.1 s) target j)
    at hmarginal
  change mme_modern_entropyBits rho ≤ mme_modern_entropyBits target
  rw [htarget] at hmarginal ⊢
  have hmax :
      mme_modern_entropyBits rho ≤
        mme_modern_entropyBits
            (fixedHashSupportDistribution fixedProfileB) + 2 * 0 := by
    apply mme_modern_entropyBits_additive_certificate
      (fun sigma : FixedHashSupportTriple ↦ sigma.1 0)
      (fun sigma : FixedHashSupportTriple ↦ sigma.1 1)
      (fun sigma : FixedHashSupportTriple ↦ sigma.1 2)
      rho (fixedHashSupportDistribution fixedProfileB)
      (-Real.log 3 / Real.log 2)
      (fixedHashSupportEntropyPotential fixedProfileB)
      (fixedHashSupportEntropyPotential fixedProfileB)
      (fixedHashSupportEntropyPotential fixedProfileB) 0
    · exact hrho
    · exact fixedHashSupportDistribution_pos fixedProfileB
        fixedHashProfileB_pos
    · exact hsum
    · exact fixedHashSupportDistribution_sum_eq_one fixedProfileB
        fixedHashProfileB_InN.1
    · exact hmarginal 0
    · exact hmarginal 1
    · exact hmarginal 2
    · norm_num
    · intro sigma
      rw [fixedHashSupportDistribution_exact_additive_potential
        fixedProfileB fixedHashProfileB_InN fixedHashProfileB_pos sigma]
      norm_num
  simpa using hmax

end MME.StothersFourth

theorem solution :
    let Omega :=
      {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8}
    let target : Omega → ℝ := fun sigma ↦
      (MME.StothersFourth.fixedJointMultiplicity 1 sigma.1 : ℝ) /
        (MME.StothersFourth.fixedOuterLength 1 : ℝ)
    ∀ rho : Omega → ℝ,
      (∀ sigma, 0 ≤ rho sigma) →
      (∑ sigma, rho sigma) = 1 →
      (∀ s : Fin 3, ∀ j : Fin 9,
        mme_modern_marginal (fun sigma : Omega ↦ sigma.1 s) rho j =
          mme_modern_marginal
            (fun sigma : Omega ↦ sigma.1 s) target j) →
      mme_modern_entropyBits rho ≤ mme_modern_entropyBits target := by
  exact MME.StothersFourth.mme_stothers_fixed_joint_entropy_maximal
