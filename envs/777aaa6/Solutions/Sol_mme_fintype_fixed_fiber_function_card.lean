-- Prove2me | solution 1 for mme_fintype_fixed_fiber_function_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:52:57.316531+00:00
-- url     : https://prove2.me/submissions/9e1c29ae-058f-4145-98e0-d31be7cf5088

import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.GroupAction.Quotient

open Equiv MulAction

set_option autoImplicit false

/-- Functions on a finite domain with the same fiber sizes as a fixed
function are counted by the corresponding multinomial coefficient. -/
theorem solution
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] (f : α → ι) :
    Fintype.card
        {g : α → ι // ∀ i,
          Fintype.card {a // g a = i} =
            Fintype.card {a // f a = i}} =
      (Fintype.card α).factorial /
        ∏ i, (Fintype.card {a // f a = i}).factorial := by
  classical
  let G := (Equiv.Perm α)ᵈᵐᵃ
  letI : Fintype G := Fintype.ofEquiv (Equiv.Perm α) DomMulAct.mk
  let P : (α → ι) → Prop := fun g => ∀ i,
    Fintype.card {a // g a = i} = Fintype.card {a // f a = i}
  have horbit : ∀ g : α → ι,
      g ∈ MulAction.orbit G f ↔ P g := by
    intro g
    constructor
    · rw [MulAction.mem_orbit_iff]
      rintro ⟨c, rfl⟩ i
      let e : {a // (c • f) a = i} ≃ {a // f a = i} :=
        Equiv.subtypeEquiv (DomMulAct.mk.symm c) (fun a => by
          change (f (DomMulAct.mk.symm c a) = i) ↔
            f (DomMulAct.mk.symm c a) = i
          rfl)
      exact Fintype.card_congr e
    · intro hg
      let e : ∀ i, {a // g a = i} ≃ {a // f a = i} :=
        fun i => Fintype.equivOfCardEq (hg i)
      let π : Equiv.Perm α := Equiv.ofFiberEquiv e
      rw [MulAction.mem_orbit_iff]
      refine ⟨DomMulAct.mk π, ?_⟩
      funext a
      change f (π a) = g a
      exact Equiv.ofFiberEquiv_map e a
  let orbitEquiv : MulAction.orbit G f ≃ {g : α → ι // P g} :=
    Equiv.subtypeEquiv (Equiv.refl (α → ι)) (fun g => by
      simpa only [Equiv.refl_apply] using horbit g)
  have horbitCard :
      Fintype.card {g : α → ι // P g} *
          Fintype.card (MulAction.stabilizer G f) =
        Fintype.card G := by
    rw [← Fintype.card_congr orbitEquiv]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group G f
  have hstab :
      Fintype.card (MulAction.stabilizer G f) =
        ∏ i, (Fintype.card {a // f a = i}).factorial := by
    let e : MulAction.stabilizer G f ≃
        {g : Equiv.Perm α // f ∘ g = f} :=
      Equiv.subtypeEquiv DomMulAct.mk.symm (fun g => by
        exact DomMulAct.mem_stabilizer_iff)
    rw [Fintype.card_congr e]
    exact DomMulAct.stabilizer_card f
  have hG : Fintype.card G = (Fintype.card α).factorial := by
    exact Fintype.card_congr DomMulAct.mk.symm |>.trans Fintype.card_perm
  change Fintype.card {g : α → ι // P g} = _
  rw [← hstab]
  exact Nat.eq_div_of_mul_eq_left (Fintype.card_ne_zero)
    (by simpa [hG] using horbitCard)
