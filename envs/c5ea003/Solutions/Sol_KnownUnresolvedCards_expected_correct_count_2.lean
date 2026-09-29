-- Prove2me | solution 2 for KnownUnresolvedCards.expected_correct_count
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:54:49.910492+00:00
-- url     : https://prove2.me/submissions/31357d8a-b61e-406b-9a81-66a6be493791

import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
import Definitions.Def_MachineLearning_KnownUnresolvedCards_NoFreeLunch
open KnownUnresolvedCards Finset in
theorem solution {X : Type*} [Fintype X] [DecidableEq X] (T : Finset X)
    (L : (X → Bool) → (X → Bool))
    (hL : ∀ f g : X → Bool, (∀ y ∈ T, f y = g y) → L f = L g)
    (hT : ∀ f : X → Bool, ∀ y ∈ T, L f y = f y) :
    E (fun f : X → Bool => ∑ y : X, (if L f y = f y then (1 : ℚ) else 0))
      = ((T.card : ℚ) + (Fintype.card X : ℚ)) / 2 := by
  have hcard : (Fintype.card (X → Bool) : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  -- flipping one coordinate is an involution of the sample space
  have hflip_inv : ∀ (y : X) (f : X → Bool), flipAt y (flipAt y f) = f := by
    intro y f
    funext z
    by_cases hz : z = y
    · subst hz
      simp [flipAt, Function.update_self]
    · simp [flipAt, Function.update_of_ne hz]
  -- off the training set the indicator is fair
  have hfair : ∀ y : X, y ∉ T →
      (∑ f : X → Bool, (if L f y = f y then (1 : ℚ) else 0))
        = (Fintype.card (X → Bool) : ℚ) / 2 := by
    intro y hy
    have hagree : ∀ f : X → Bool, L (flipAt y f) = L f := by
      intro f
      refine hL _ _ (fun z hz => ?_)
      have hzy : z ≠ y := fun h => hy (h ▸ hz)
      simp [flipAt, Function.update_of_ne hzy]
    have hval : ∀ f : X → Bool, (flipAt y f) y = !(f y) := by
      intro f
      simp [flipAt, Function.update_self]
    let e : (X → Bool) ≃ (X → Bool) :=
      { toFun := flipAt y, invFun := flipAt y,
        left_inv := hflip_inv y, right_inv := hflip_inv y }
    have hswap : (∑ f : X → Bool, (if L f y = f y then (1 : ℚ) else 0))
        = ∑ f : X → Bool, (1 - (if L f y = f y then (1 : ℚ) else 0)) := by
      calc (∑ f : X → Bool, (if L f y = f y then (1 : ℚ) else 0))
          = ∑ f : X → Bool, (if L (e f) y = (e f) y then (1 : ℚ) else 0) :=
            (Equiv.sum_comp e (fun f => if L f y = f y then (1 : ℚ) else 0)).symm
        _ = ∑ f : X → Bool, (1 - (if L f y = f y then (1 : ℚ) else 0)) := by
            refine Finset.sum_congr rfl (fun f _ => ?_)
            show (if L (flipAt y f) y = (flipAt y f) y then (1 : ℚ) else 0)
              = 1 - (if L f y = f y then (1 : ℚ) else 0)
            rw [hagree f, hval f]
            cases hLf : L f y <;> cases hff : f y <;> norm_num
    have h2 : 2 * (∑ f : X → Bool, (if L f y = f y then (1 : ℚ) else 0))
        = (Fintype.card (X → Bool) : ℚ) := by
      have := hswap
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one] at this
      linarith
    linarith
  -- on the training set the indicator is certain
  have hcert : ∀ y : X, y ∈ T →
      (∑ f : X → Bool, (if L f y = f y then (1 : ℚ) else 0))
        = (Fintype.card (X → Bool) : ℚ) := by
    intro y hy
    have : ∀ f : X → Bool, (if L f y = f y then (1 : ℚ) else 0) = 1 := by
      intro f
      rw [if_pos (hT f y hy)]
    rw [Finset.sum_congr rfl (fun f _ => this f), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  -- assemble
  unfold E
  rw [Finset.sum_comm]
  have hrow : ∀ y : X, (∑ f : X → Bool, (if L f y = f y then (1 : ℚ) else 0))
      = (if y ∈ T then (Fintype.card (X → Bool) : ℚ)
          else (Fintype.card (X → Bool) : ℚ) / 2) := by
    intro y
    by_cases hy : y ∈ T
    · rw [if_pos hy, hcert y hy]
    · rw [if_neg hy, hfair y hy]
  rw [Finset.sum_congr rfl (fun y _ => hrow y)]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter, nsmul_eq_mul, nsmul_eq_mul]
  have hcompl : ((Finset.univ.filter (fun y : X => y ∉ T)).card : ℚ)
      = (Fintype.card X : ℚ) - (T.card : ℚ) := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset X))
      (p := fun y => y ∈ T)
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ] at h
    have : T.card + (Finset.univ.filter (fun y : X => y ∉ T)).card = Fintype.card X := h
    push_cast [← this]
    ring
  rw [hcompl]
  field_simp
  ring
