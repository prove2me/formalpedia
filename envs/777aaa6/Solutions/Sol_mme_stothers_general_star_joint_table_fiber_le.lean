-- Prove2me | solution 1 for mme_stothers_general_star_joint_table_fiber_le
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T05:35:32.811761+00:00
-- url     : https://prove2.me/submissions/33334f4d-445c-4acf-a76c-ee7d5180ce2f

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_general_mode_joint_table_fiber_card
import Theorems.Thm_mme_stothers_general_completion_quotient_le_polynomial_target

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

namespace MME.StothersFourth

private theorem genHashReduction_card_composite_fiber
    {alpha beta iota : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta] [DecidableEq iota]
    (g : alpha → beta) (q : beta → iota) (r : iota) :
    Fintype.card {x : alpha // q (g x) = r} =
      ∑ y : {y : beta // q y = r},
        Fintype.card {x : alpha // g x = y.1} := by
  classical
  let e : {x : alpha // q (g x) = r} ≃
      Sigma fun y : {y : beta // q y = r} ↦
        {x : alpha // g x = y.1} := {
    toFun x := ⟨⟨g x.1, x.2⟩, ⟨x.1, rfl⟩⟩
    invFun x := ⟨x.2.1, by rw [x.2.2, x.1.2]⟩
    left_inv x := by
      apply Subtype.ext
      rfl
    right_inv x := by
      rcases x with ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
      cases hx
      rfl
  }
  rw [Fintype.card_congr e, Fintype.card_sigma]

private theorem genHashReduction_joint_table_marginal
    {base : Fin 10 → ℕ} {m : ℕ} (a : GenMarginalSupportedAddress base m)
    (i : Fin 3) (j : Fin 9) :
    (∑ sigma : {sigma : GenHashSupportTriple // sigma.1 i = j},
      genHashJointTable a sigma.1) = genMarginalCount base m j := by
  classical
  unfold genHashJointTable
  rw [← genHashReduction_card_composite_fiber
    (fun r ↦ genHashSupportedTypeAt a r)
    (fun sigma : GenHashSupportTriple ↦ sigma.1 i) j]
  rw [Fintype.card_subtype]
  exact a.2.2 i j


end MME.StothersFourth

theorem solution
    (base bstar : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ r, 0 < base r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (hcond : ∀ k : MME.StothersFourth.GenHashJointMultiplicityTable,
      (∀ l : Fin 3, ∀ j : Fin 9,
        (∑ sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
          sigma.1 l = j}, k sigma.1) =
          MME.StothersFourth.genMarginalCount base m j) →
      ∀ i : Fin 3,
      (∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
              sigma.1 i = j} ↦
            (k sigma.1 : ℝ) /
              (MME.StothersFourth.genMarginalCount base m j : ℝ))) ≤
      ∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
              sigma.1 i = j} ↦
            (MME.StothersFourth.genHashTargetJointTable bstar m sigma.1 : ℝ) /
              (MME.StothersFourth.genMarginalCount base m j : ℝ)))
    (E : Finset (MME.StothersFourth.GenMarginalSupportedAddress base m))
    (a : MME.StothersFourth.GenMarginalSupportedAddress base m) (i : Fin 3)
    (k : MME.StothersFourth.GenHashJointMultiplicityTable)
    (hk : k ∈ (E.filter (fun b ↦ b.1 i = a.1 i)).image
      MME.StothersFourth.genHashJointTable) :
    ((E.filter (fun b ↦ b.1 i = a.1 i)).filter
      (fun b ↦ MME.StothersFourth.genHashJointTable b = k)).card ≤
        (6 * (MME.StothersFourth.genOuterLength base m + 1)) ^ 45 *
          MME.StothersFourth.genHashTargetStarDegree bstar m := by
  classical
  let : Finite (MME.StothersFourth.GenOuterAddress base m) :=
    inferInstanceAs (Finite
      (Fin 3 → Fin (MME.StothersFourth.genOuterLength base m) → Fin 9))
  let : Finite (MME.StothersFourth.GenMarginalSupportedAddress base m) :=
    Subtype.finite
  let Star := E.filter (fun b ↦ b.1 i = a.1 i)
  change (Star.filter
    (fun b ↦ MME.StothersFourth.genHashJointTable b = k)).card ≤ _
  have hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
          sigma.1 l = j}, k sigma.1) =
        MME.StothersFourth.genMarginalCount base m j := by
    intro l j
    change k ∈ Star.image MME.StothersFourth.genHashJointTable at hk
    rcases Finset.mem_image.mp hk with ⟨b, hb, rfl⟩
    exact MME.StothersFourth.genHashReduction_joint_table_marginal b l j
  let Fiber :=
    {b : MME.StothersFourth.GenMarginalSupportedAddress base m //
      b ∈ Star.filter
        (fun b ↦ MME.StothersFourth.genHashJointTable b = k)}
  let f : Fiber →
      {b : MME.StothersFourth.GenMarginalSupportedAddress base m //
        b.1 i = a.1 i ∧
          MME.StothersFourth.genHashJointTable b = k} := fun b ↦ by
    have hb := Finset.mem_filter.mp b.2
    have hbStar := Finset.mem_filter.mp hb.1
    exact ⟨b.1, hbStar.2, hb.2⟩
  have hf : Function.Injective f := by
    intro b c h
    dsimp only [f] at h
    have hval : b.1 = c.1 := congrArg
      (fun x : {b : MME.StothersFourth.GenMarginalSupportedAddress base m //
        b.1 i = a.1 i ∧
          MME.StothersFourth.genHashJointTable b = k} ↦ x.1) h
    exact Subtype.ext hval
  have hcardLe :
      (Star.filter
        (fun b ↦ MME.StothersFourth.genHashJointTable b = k)).card ≤
        Nat.card
          {b : MME.StothersFourth.GenMarginalSupportedAddress base m //
            b.1 i = a.1 i ∧
              MME.StothersFourth.genHashJointTable b = k} := by
    calc
      (Star.filter
          (fun b ↦ MME.StothersFourth.genHashJointTable b = k)).card =
          Fintype.card Fiber := by
        simpa only [Fiber] using
          (Fintype.card_coe
            (Star.filter
              (fun b ↦ MME.StothersFourth.genHashJointTable b = k))).symm
      _ = Nat.card Fiber := by
        rw [Nat.card_eq_fintype_card]
      _ ≤ Nat.card
          {b : MME.StothersFourth.GenMarginalSupportedAddress base m //
            b.1 i = a.1 i ∧
              MME.StothersFourth.genHashJointTable b = k} :=
        Nat.card_le_card_of_injective f hf
  have hquotReal :=
    mme_stothers_general_completion_quotient_le_polynomial_target
      base bstar m hm hbase hsame i k hkMarginal (hcond k hkMarginal i)
  have hquotNat :
      (∏ j : Fin 9,
          (MME.StothersFourth.genMarginalCount base m j).factorial) /
          ∏ sigma : MME.StothersFourth.GenHashSupportTriple,
            (k sigma).factorial ≤
        (6 * (MME.StothersFourth.genOuterLength base m + 1)) ^ 45 *
          MME.StothersFourth.genHashTargetStarDegree bstar m := by
    apply (Nat.cast_le (α := ℝ)).mp
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] using hquotReal
  calc
    (Star.filter
        (fun b ↦ MME.StothersFourth.genHashJointTable b = k)).card ≤
        Nat.card
          {b : MME.StothersFourth.GenMarginalSupportedAddress base m //
            b.1 i = a.1 i ∧
              MME.StothersFourth.genHashJointTable b = k} := hcardLe
    _ = (∏ j : Fin 9,
          (MME.StothersFourth.genMarginalCount base m j).factorial) /
        ∏ sigma : MME.StothersFourth.GenHashSupportTriple,
          (k sigma).factorial :=
      mme_stothers_general_mode_joint_table_fiber_card
        base m a i k hkMarginal
    _ ≤ (6 * (MME.StothersFourth.genOuterLength base m + 1)) ^ 45 *
        MME.StothersFourth.genHashTargetStarDegree bstar m := hquotNat

