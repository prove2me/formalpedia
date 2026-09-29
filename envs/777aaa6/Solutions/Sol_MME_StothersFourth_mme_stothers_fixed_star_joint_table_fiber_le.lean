-- Prove2me | solution 1 for MME.StothersFourth.mme_stothers_fixed_star_joint_table_fiber_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:58:36.645132+00:00
-- url     : https://prove2.me/submissions/542f433f-db69-4027-ae45-ad70fdf3f6e9

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_mode_joint_table_fiber_card
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_completion_quotient_le_polynomial_target

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

namespace MME.StothersFourth

private theorem fixedHashReduction_card_composite_fiber
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

private theorem fixedHashReduction_joint_table_marginal
    {m : ℕ} (a : FixedMarginalSupportedAddress m)
    (i : Fin 3) (j : Fin 9) :
    (∑ sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j},
      fixedHashJointTable a sigma.1) = fixedMarginalCount m j := by
  classical
  unfold fixedHashJointTable
  rw [← fixedHashReduction_card_composite_fiber
    (fun r ↦ fixedHashSupportedTypeAt a r)
    (fun sigma : FixedHashSupportTriple ↦ sigma.1 i) j]
  rw [Fintype.card_subtype]
  simpa only [fixedHashSupportedTypeAt] using a.2.2 i j

end MME.StothersFourth

theorem solution
    (m : ℕ) (hm : 0 < m)
    (E : Finset (MME.StothersFourth.FixedMarginalSupportedAddress m))
    (a : MME.StothersFourth.FixedMarginalSupportedAddress m) (i : Fin 3)
    (k : MME.StothersFourth.FixedHashJointMultiplicityTable)
    (hk : k ∈ (E.filter (fun b ↦ b.1 i = a.1 i)).image
      MME.StothersFourth.fixedHashJointTable) :
    ((E.filter (fun b ↦ b.1 i = a.1 i)).filter
      (fun b ↦ MME.StothersFourth.fixedHashJointTable b = k)).card ≤
        (6 * (MME.StothersFourth.fixedOuterLength m + 1)) ^ 45 *
          MME.StothersFourth.fixedHashTargetStarDegree m := by
  classical
  letI : Finite (MME.StothersFourth.FixedOuterAddress m) :=
    inferInstanceAs (Finite
      (Fin 3 → Fin (MME.StothersFourth.fixedOuterLength m) → Fin 9))
  letI : Finite (MME.StothersFourth.FixedMarginalSupportedAddress m) :=
    Subtype.finite
  let Star := E.filter (fun b ↦ b.1 i = a.1 i)
  change (Star.filter
    (fun b ↦ MME.StothersFourth.fixedHashJointTable b = k)).card ≤ _
  have hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple //
          sigma.1 l = j}, k sigma.1) =
        MME.StothersFourth.fixedMarginalCount m j := by
    intro l j
    change k ∈ Star.image MME.StothersFourth.fixedHashJointTable at hk
    rcases Finset.mem_image.mp hk with ⟨b, hb, rfl⟩
    exact MME.StothersFourth.fixedHashReduction_joint_table_marginal b l j
  let Fiber :=
    {b : MME.StothersFourth.FixedMarginalSupportedAddress m //
      b ∈ Star.filter
        (fun b ↦ MME.StothersFourth.fixedHashJointTable b = k)}
  let f : Fiber →
      {b : MME.StothersFourth.FixedMarginalSupportedAddress m //
        b.1 i = a.1 i ∧
          MME.StothersFourth.fixedHashJointTable b = k} := fun b ↦ by
    have hb := Finset.mem_filter.mp b.2
    have hbStar := Finset.mem_filter.mp hb.1
    exact ⟨b.1, hbStar.2, hb.2⟩
  have hf : Function.Injective f := by
    intro b c h
    dsimp only [f] at h
    have hval : b.1 = c.1 := congrArg
      (fun x : {b : MME.StothersFourth.FixedMarginalSupportedAddress m //
        b.1 i = a.1 i ∧
          MME.StothersFourth.fixedHashJointTable b = k} ↦ x.1) h
    exact Subtype.ext hval
  have hcardLe :
      (Star.filter
        (fun b ↦ MME.StothersFourth.fixedHashJointTable b = k)).card ≤
        Nat.card
          {b : MME.StothersFourth.FixedMarginalSupportedAddress m //
            b.1 i = a.1 i ∧
              MME.StothersFourth.fixedHashJointTable b = k} := by
    calc
      (Star.filter
          (fun b ↦ MME.StothersFourth.fixedHashJointTable b = k)).card =
          Fintype.card Fiber := by
        simpa only [Fiber] using
          (Fintype.card_coe
            (Star.filter
              (fun b ↦ MME.StothersFourth.fixedHashJointTable b = k))).symm
      _ = Nat.card Fiber := by
        rw [Nat.card_eq_fintype_card]
      _ ≤ Nat.card
          {b : MME.StothersFourth.FixedMarginalSupportedAddress m //
            b.1 i = a.1 i ∧
              MME.StothersFourth.fixedHashJointTable b = k} :=
        Nat.card_le_card_of_injective f hf
  have hquotReal :=
    MME.StothersFourth.mme_stothers_fixed_completion_quotient_le_polynomial_target
      m hm i k hkMarginal
  have hquotNat :
      (∏ j : Fin 9,
          (MME.StothersFourth.fixedMarginalCount m j).factorial) /
          ∏ sigma : MME.StothersFourth.FixedHashSupportTriple,
            (k sigma).factorial ≤
        (6 * (MME.StothersFourth.fixedOuterLength m + 1)) ^ 45 *
          MME.StothersFourth.fixedHashTargetStarDegree m := by
    apply (Nat.cast_le (α := ℝ)).mp
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] using hquotReal
  calc
    (Star.filter
        (fun b ↦ MME.StothersFourth.fixedHashJointTable b = k)).card ≤
        Nat.card
          {b : MME.StothersFourth.FixedMarginalSupportedAddress m //
            b.1 i = a.1 i ∧
              MME.StothersFourth.fixedHashJointTable b = k} := hcardLe
    _ = (∏ j : Fin 9,
          (MME.StothersFourth.fixedMarginalCount m j).factorial) /
        ∏ sigma : MME.StothersFourth.FixedHashSupportTriple,
          (k sigma).factorial :=
      MME.StothersFourth.mme_stothers_fixed_mode_joint_table_fiber_card
        m a i k hkMarginal
    _ ≤ (6 * (MME.StothersFourth.fixedOuterLength m + 1)) ^ 45 *
        MME.StothersFourth.fixedHashTargetStarDegree m := hquotNat
