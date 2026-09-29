-- Prove2me | solution 1 for mme_stothers_fixed_profile_fourth_value_of_capacity_and_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:36:54.059033+00:00
-- url     : https://prove2.me/submissions/80c58da6-f5f9-4bed-97ad-b89adeb57351

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_fixed_outer_profile
import Theorems.Thm_mme_induced_graded_address_blocks_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_bigAdd_uniform_strict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_kronPow_root
import Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss

open MME BigOperators Filter Topology

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth

private theorem fixedMixedAddress_apply
    {m : ℕ} (x y z : FixedOuterAddress m) (s : Fin 3) :
    fixedMixedAddress x y z s = ![x 0, y 1, z 2] s := by
  fin_cases s <;> rfl

/-- The fixed-profile specialization of the generic induced-word zeroing
lemma.  This is the complete tensor-zeroing part of the outer laser: once an
induced exact-profile family has been selected, all mixed address blocks
vanish and the surviving exact blocks form a direct sum. -/
theorem mme_stothers_fixed_induced_address_blocks_restrict
    {K : Type u} [Field K]
    (m : ℕ) (F : Finset (FixedExactOuterAddress m))
    (hF : FixedInducedModeDisjoint F)
    (hblockSupport : ∀ sigma : Fin 3 → Fin 9,
      (cwFourthCanonicalGrading K 6).blockTensor sigma ≠ 0 →
        (∑ s, ((sigma s).val : ℕ)) = 8) :
    ∃ e : Fin F.card ≃ F,
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦
          gradedAddressBlock (cwFourthCanonicalGrading K 6) (e j).1.1))
        ((cwFourthObj K 6).kronPow (fixedOuterLength m)) := by
  classical
  let e : Fin F.card ≃ F := by
    simpa only [Fintype.card_coe] using (Fintype.equivFin F).symm
  refine ⟨e, mme_induced_graded_address_blocks_restrict
    (cwFourthCanonicalGrading K 6)
    (fun j ↦ (e j).1.1) ?_⟩
  intro js hnonzero
  have hsupported : FixedCoordinatewiseSupported
      (fixedMixedAddress (e (js 0)).1.1
        (e (js 1)).1.1 (e (js 2)).1.1) := by
    intro k
    have h := hblockSupport
      (fun s ↦ (e (js s)).1.1 s k) (hnonzero k)
    simpa only [FixedCoordinatewiseSupported, fixedMixedAddress_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] using h
  obtain ⟨h01, h12⟩ := hF.2
    (e (js 0)) (e (js 1)) (e (js 2)) hsupported
  have hj01 : js 0 = js 1 := e.injective h01
  have hj12 : js 1 = js 2 := e.injective h12
  refine ⟨js 0, ?_⟩
  funext s
  fin_cases s
  · rfl
  · exact hj01.symm
  · exact (hj01.trans hj12).symm

/-- The exact inner contribution of one fixed Stothers address at scale
`m`.  There are `3 * classMultiplicity r` ordered constituents in class
`r`; grouping them into cyclic triples leaves
`classMultiplicity r * fixedProfileCount m r` cyclic factors. -/
private noncomputable def fixedInnerWeight (tau : ℝ) (m : ℕ) : ℝ :=
  ∏ r : Fin 10,
    (classValue 6 tau r) ^
      (classMultiplicity r * fixedProfileCount m r)

/-- A minimal and source-faithful assembly interface for the fixed-profile
fourth-power theorem.  The first premise is precisely the outer
hash/Stirling capacity estimate.  The second is precisely the exact-address
inner extraction obtained by cyclic regrouping and Lemma 5.1.  Everything
else—induced-word zeroing, direct-sum additivity, transport through a
restriction, and taking the `N`th root—is proved here. -/
theorem mme_stothers_fixed_profile_fourth_value_of_capacity_and_blocks
    {K : Type u} [Field K]
    (tau : ℝ)
    (hblockSupport : ∀ sigma : Fin 3 → Fin 9,
      (cwFourthCanonicalGrading K 6).blockTensor sigma ≠ 0 →
        (∑ s, ((sigma s).val : ℕ)) = 8)
    (hcapacity : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ F : Finset (FixedExactOuterAddress m),
          FixedInducedModeDisjoint F ∧
          (globalRate 6 tau fixedProfileB fixedProfileB) ^
                (fixedOuterLength m) *
              Real.exp
                (-C * Real.sqrt
                  (((fixedOuterLength m + 1 : ℕ) : ℝ))) ≤
            (F.card : ℝ) *
              (∏ r : Fin 10,
                (classValue 6 tau r) ^
                  (classMultiplicity r * fixedProfileCount m r)))
    (hblocks : ∀ (m : ℕ) (a : FixedExactOuterAddress m)
        (W : ℝ),
      0 ≤ W →
      W < (∏ r : Fin 10,
        (classValue 6 tau r) ^
          (classMultiplicity r * fixedProfileCount m r)) →
      HasTauValueAtLeast
        (gradedAddressBlock (cwFourthCanonicalGrading K 6) a.1)
        tau W) :
    ∀ V : ℝ, 0 ≤ V →
      V < globalRate 6 tau fixedProfileB fixedProfileB →
      HasTauValueAtLeast (cwFourthObj K 6) tau V := by
  rcases hcapacity with ⟨C, hC, hcapacity⟩
  intro V hV hVglobal
  let G : ℝ := globalRate 6 tau fixedProfileB fixedProfileB
  let W : ℝ := (V + G) / 2
  have hVG : V < G := by simpa only [G] using hVglobal
  have hVW : V < W := by
    dsimp only [W]
    linarith
  have hWG : W < G := by
    dsimp only [W]
    linarith
  have hW : 0 ≤ W := hV.trans hVW.le
  have hgapN :
      ∀ᶠ N : ℕ in atTop,
        W ^ N ≤ G ^ N *
          Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) :=
    mme_strict_pow_absorbs_sqrt_exp_loss W G C hW hWG hC
  have hlength : Tendsto fixedOuterLength atTop atTop := by
    unfold fixedOuterLength
    have hm : Tendsto (fun m : ℕ ↦ fixedProfileScale * m)
        atTop atTop := by
      simpa [nsmul_eq_mul, mul_comm] using
        ((tendsto_id : Tendsto (fun x : ℕ ↦ x) atTop atTop).nsmul_atTop
          (by norm_num [fixedProfileScale] : 0 < fixedProfileScale))
    simpa [nsmul_eq_mul, mul_comm] using
      hm.nsmul_atTop (by norm_num : 0 < 3)
  have hgapM :
      ∀ᶠ m : ℕ in atTop,
        W ^ (fixedOuterLength m) ≤
          G ^ (fixedOuterLength m) *
            Real.exp (-C * Real.sqrt
              (((fixedOuterLength m + 1 : ℕ) : ℝ))) :=
    hlength.eventually hgapN
  have hmpos : ∀ᶠ m : ℕ in atTop, 0 < m := eventually_gt_atTop 0
  obtain ⟨m, hmcap, hmgap, hmpos⟩ :=
    (hcapacity.and (hgapM.and hmpos)).exists
  obtain ⟨F, hF, hcap⟩ := hmcap
  let N : ℕ := fixedOuterLength m
  let P : ℝ := fixedInnerWeight tau m
  have hN : 0 < N := by
    dsimp only [N, fixedOuterLength]
    have hs : 0 < fixedProfileScale := by
      norm_num [fixedProfileScale]
    positivity
  have hVpowWpow : V ^ N < W ^ N :=
    pow_lt_pow_left₀ hVW hV hN.ne'
  have hVpowCapacity :
      V ^ N < (F.card : ℝ) * P := by
    calc
      V ^ N < W ^ N := hVpowWpow
      _ ≤ G ^ N * Real.exp
          (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
        simpa only [N] using hmgap
      _ ≤ (F.card : ℝ) * P := by
        simpa only [G, N, P, fixedInnerWeight] using hcap
  have hinnerNonneg : 0 ≤ P := by
    by_cases hFzero : F.card = 0
    · simp [hFzero] at hVpowCapacity
      exact False.elim ((not_lt_of_ge (pow_nonneg hV N)) hVpowCapacity)
    · have hcardPos : (0 : ℝ) < F.card := by
        exact_mod_cast (Nat.pos_of_ne_zero hFzero)
      by_contra hneg
      have hinnerNeg : P < 0 := lt_of_not_ge hneg
      have hprodNeg : (F.card : ℝ) * P < 0 :=
        mul_neg_of_pos_of_neg hcardPos hinnerNeg
      exact (not_lt_of_ge (pow_nonneg hV N))
        (hVpowCapacity.trans hprodNeg)
  obtain ⟨e, hzeroing⟩ :=
    mme_stothers_fixed_induced_address_blocks_restrict
      m F hF hblockSupport
  have hsum : HasTauValueAtLeast
      (TensorObj.bigAdd (fun j ↦
        gradedAddressBlock (cwFourthCanonicalGrading K 6) (e j).1.1))
      tau (V ^ N) := by
    apply mme_HasTauValueAtLeast_bigAdd_uniform_strict
      (fun j ↦
        gradedAddressBlock (cwFourthCanonicalGrading K 6) (e j).1.1)
      tau P hinnerNonneg
    · intro j U hU hUstrict
      simpa only [P, fixedInnerWeight] using
        hblocks m (e j).1 U hU hUstrict
    · exact pow_nonneg hV N
    · simpa only [N] using hVpowCapacity
  have hpower : HasTauValueAtLeast
      ((cwFourthObj K 6).kronPow N) tau (V ^ N) :=
    mme_HasTauValueAtLeast_mono_restrict hzeroing hsum
  exact mme_HasTauValueAtLeast_kronPow_root
    (cwFourthObj K 6) tau V N hN hV hpower

end MME.StothersFourth

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ)
    (hblockSupport : ∀ sigma : Fin 3 → Fin 9,
      (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockTensor sigma ≠ 0 →
        (∑ s, ((sigma s).val : ℕ)) = 8)
    (hcapacity : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in Filter.atTop,
        ∃ F : Finset (MME.StothersFourth.FixedExactOuterAddress m),
          MME.StothersFourth.FixedInducedModeDisjoint F ∧
          (MME.StothersFourth.globalRate 6 tau
                MME.StothersFourth.fixedProfileB
                MME.StothersFourth.fixedProfileB) ^
                (MME.StothersFourth.fixedOuterLength m) *
              Real.exp
                (-C * Real.sqrt
                  (((MME.StothersFourth.fixedOuterLength m + 1 : ℕ) : ℝ))) ≤
            (F.card : ℝ) *
              (∏ r : Fin 10,
                (MME.StothersFourth.classValue 6 tau r) ^
                  (MME.StothersFourth.classMultiplicity r *
                    MME.StothersFourth.fixedProfileCount m r)))
    (hblocks : ∀ (m : ℕ)
        (a : MME.StothersFourth.FixedExactOuterAddress m) (W : ℝ),
      0 ≤ W →
      W < (∏ r : Fin 10,
        (MME.StothersFourth.classValue 6 tau r) ^
          (MME.StothersFourth.classMultiplicity r *
            MME.StothersFourth.fixedProfileCount m r)) →
      HasTauValueAtLeast
        (gradedAddressBlock
          (MME.StothersFourth.cwFourthCanonicalGrading K 6) a.1)
        tau W) :
    ∀ V : ℝ, 0 ≤ V →
      V < MME.StothersFourth.globalRate 6 tau
        MME.StothersFourth.fixedProfileB
        MME.StothersFourth.fixedProfileB →
      HasTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 6) tau V := by
  exact
    MME.StothersFourth.mme_stothers_fixed_profile_fourth_value_of_capacity_and_blocks
      tau hblockSupport hcapacity hblocks
