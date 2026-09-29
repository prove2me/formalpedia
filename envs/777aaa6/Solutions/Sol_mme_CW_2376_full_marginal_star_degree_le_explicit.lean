-- Prove2me | solution 1 for mme_CW_2376_full_marginal_star_degree_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T23:37:38.001396+00:00
-- url     : https://prove2.me/submissions/774c2524-43f3-4729-9567-a8ab024d8b43

import Definitions.Def_mme_CW_2376_marginal_joint_tables
import Theorems.Thm_mme_CW_2376_fixed_mode_joint_table_fiber_card
import Theorems.Thm_mme_CW_2376_target_table_factorial_dominates
import Theorems.Thm_mme_bounded_natural_table_family_card_le

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem card_composite_fiber
    {alpha beta iota : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta] [DecidableEq iota]
    (g : alpha → beta) (q : beta → iota) (i : iota) :
    Fintype.card {a : alpha // q (g a) = i} =
      ∑ b : {b : beta // q b = i},
        Fintype.card {a : alpha // g a = b.1} := by
  classical
  let e : {a : alpha // q (g a) = i} ≃
      Sigma fun b : {b : beta // q b = i} =>
        {a : alpha // g a = b.1} := {
    toFun a := ⟨⟨g a.1, a.2⟩, ⟨a.1, rfl⟩⟩
    invFun a := ⟨a.2.1, by rw [a.2.2, a.1.2]⟩
    left_inv a := by
      apply Subtype.ext
      rfl
    right_inv a := by
      rcases a with ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
      cases ha
      rfl
  }
  rw [Fintype.card_congr e, Fintype.card_sigma]

private theorem marginal_joint_table_marginal
    {m : ℕ} (a : CW2376MarginalSupportedAddress m)
    (i : Fin 3) (r : Fin 5) :
    (∑ sigma : {sigma : CW2376SupportedJointType // sigma.1 i = r},
      cw2376MarginalJointTable a sigma.1) =
        cw2376MarginalMultiplicity m r := by
  classical
  unfold cw2376MarginalJointTable
  rw [← card_composite_fiber
    (fun j => cw2376MarginalSupportedJointTypeAt a j)
    (fun sigma : CW2376SupportedJointType => sigma.1 i) r]
  rw [Fintype.card_subtype]
  simpa only [cw2376MarginalSupportedJointTypeAt,
    cw2376AddressType] using a.2.2 i r

private theorem supported_joint_type_card :
    Fintype.card CW2376SupportedJointType = 15 := by
  decide

/-- Every full marginal-supported star has degree at most the polynomial
number of compatible joint tables times the optimized target completion
degree. -/
theorem solution
    (m : ℕ) (hm : 0 < m)
    (a : CW2376MarginalSupportedAddress m) (i : Fin 3) :
    ((cw2376MarginalSupportedUniverse m).filter
      (fun b => b.1 i = a.1 i)).card ≤
      (cw2376ProfileLength m + 1) ^ 15 *
        ((∏ r : Fin 5,
            (cw2376MarginalMultiplicity m r).factorial) /
          ∏ sigma : CW2376SupportedJointType,
            (cw2376TargetJointTable m sigma).factorial) := by
  classical
  letI : Fintype (CW2376ProfileAddress m) :=
    inferInstanceAs (Fintype
      (Fin 3 → Fin (cw2376ProfileLength m) → Fin 5))
  letI : Fintype (CW2376MarginalSupportedAddress m) :=
    inferInstanceAs (Fintype
      {a : CW2376ProfileAddress m //
        CW2376CoordinatewiseSupported a ∧ CW2376MarginallyRegular a})
  let N := cw2376ProfileLength m
  let Star := (cw2376MarginalSupportedUniverse m).filter
    (fun b => b.1 i = a.1 i)
  let Tables := Star.image cw2376MarginalJointTable
  let Dstar :=
    (∏ r : Fin 5, (cw2376MarginalMultiplicity m r).factorial) /
      ∏ sigma : CW2376SupportedJointType,
        (cw2376TargetJointTable m sigma).factorial
  change Star.card ≤ (N + 1) ^ 15 * Dstar

  have hfiber : ∀ k ∈ Tables,
      (Star.filter (fun b => cw2376MarginalJointTable b = k)).card ≤
        Dstar := by
    intro k hk
    have hkMarginal : ∀ l : Fin 3, ∀ r : Fin 5,
        (∑ sigma : {sigma : CW2376SupportedJointType //
            sigma.1 l = r}, k sigma.1) =
          cw2376MarginalMultiplicity m r := by
      intro l r
      rcases Finset.mem_image.mp hk with ⟨b, hb, rfl⟩
      exact marginal_joint_table_marginal b l r
    let AddressClass :=
      {b : CW2376MarginalSupportedAddress m //
        b.1 i = a.1 i ∧ cw2376MarginalJointTable b = k}
    let Fiber :=
      {b : CW2376MarginalSupportedAddress m //
        b ∈ Star.filter (fun b => cw2376MarginalJointTable b = k)}
    let e : Fiber ≃ AddressClass := {
      toFun b := by
        have hb := Finset.mem_filter.mp b.2
        have hbStar := Finset.mem_filter.mp hb.1
        exact ⟨b.1, hbStar.2, hb.2⟩
      invFun b := ⟨b.1, by
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_filter.mpr
          exact ⟨by simp [cw2376MarginalSupportedUniverse], b.2.1⟩
        · exact b.2.2⟩
      left_inv b := by
        apply Subtype.ext
        rfl
      right_inv b := by
        apply Subtype.ext
        rfl
    }
    have hcardLe :
        (Star.filter (fun b => cw2376MarginalJointTable b = k)).card ≤
          Nat.card AddressClass := by
      calc
        (Star.filter (fun b => cw2376MarginalJointTable b = k)).card =
            Fintype.card Fiber := by
          simpa only [Fiber] using
            (Fintype.card_coe
              (Star.filter (fun b => cw2376MarginalJointTable b = k))).symm
        _ = Nat.card AddressClass := by
          rw [← Nat.card_eq_fintype_card]
          exact Nat.card_congr e
        _ ≤ Nat.card AddressClass := le_rfl
    have hclass : Nat.card AddressClass =
        (∏ r : Fin 5, (cw2376MarginalMultiplicity m r).factorial) /
          ∏ sigma : CW2376SupportedJointType,
            (k sigma).factorial := by
      simpa only [AddressClass] using
        (mme_CW_2376_fixed_mode_joint_table_fiber_card
          m a i k hkMarginal)
    have hden := mme_CW_2376_target_table_factorial_dominates
      m hm k hkMarginal
    have htargetDenPos :
        0 < ∏ sigma : CW2376SupportedJointType,
          (cw2376TargetJointTable m sigma).factorial := by
      exact Finset.prod_pos fun sigma hsigma => Nat.factorial_pos _
    have hquot := Nat.div_le_div_left
      (a := ∏ r : Fin 5, (cw2376MarginalMultiplicity m r).factorial)
      hden htargetDenPos
    calc
      (Star.filter (fun b => cw2376MarginalJointTable b = k)).card ≤
          Nat.card AddressClass := hcardLe
      _ = (∏ r : Fin 5,
            (cw2376MarginalMultiplicity m r).factorial) /
          ∏ sigma : CW2376SupportedJointType,
            (k sigma).factorial := hclass
      _ ≤ (∏ r : Fin 5,
            (cw2376MarginalMultiplicity m r).factorial) /
          ∏ sigma : CW2376SupportedJointType,
            (cw2376TargetJointTable m sigma).factorial := hquot
      _ = Dstar := by rfl

  have hTableBound : Tables.card ≤ (N + 1) ^ 15 := by
    have h := mme_bounded_natural_table_family_card_le Tables N (by
      intro k hk sigma
      rcases Finset.mem_image.mp hk with ⟨b, hb, rfl⟩
      change Fintype.card
        {j : Fin (cw2376ProfileLength m) //
          cw2376MarginalSupportedJointTypeAt b j = sigma} ≤ N
      simpa only [N, Fintype.card_fin] using
        (Fintype.card_subtype_le
          (fun j : Fin (cw2376ProfileLength m) =>
            cw2376MarginalSupportedJointTypeAt b j = sigma)))
    simpa only [supported_joint_type_card] using h
  have hStar := Finset.card_le_mul_card_image Star Dstar hfiber
  calc
    Star.card ≤ Dstar * Tables.card := hStar
    _ ≤ Dstar * (N + 1) ^ 15 := Nat.mul_le_mul_left Dstar hTableBound
    _ = (N + 1) ^ 15 * Dstar := by ac_rfl
