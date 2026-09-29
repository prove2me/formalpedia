-- Prove2me | solution 2 for KnownUnresolvedCards.no_free_lunch_kary_expected_score
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:59:13.421687+00:00
-- url     : https://prove2.me/submissions/4bacc533-09bf-47a1-8b5b-beed7620e81f

import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
import Definitions.Def_MachineLearning_KnownUnresolvedCards_NoFreeLunch
open KnownUnresolvedCards Finset in
theorem solution {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} [NeZero k] (T : Finset X)
    (L : (X → ZMod k) → (X → ZMod k))
    (hL : ∀ f g : X → ZMod k, (∀ y ∈ T, f y = g y) → L f = L g)
    (hT : ∀ f : X → ZMod k, ∀ y ∈ T, L f y = f y) :
    E (fun f : X → ZMod k => ∑ y : X, (if L f y = f y then ((k : ℚ) - 1) else -1))
      = ((k : ℚ) - 1) * (T.card : ℚ) := by
  have hkQ : (k : ℚ) ≠ 0 := by
    have : k ≠ 0 := NeZero.ne k
    exact_mod_cast this
  have hcard : (Fintype.card (X → ZMod k) : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  have hsi : ∀ (y : X) (t : ZMod k) (f : X → ZMod k), shiftBy y (-t) (shiftBy y t f) = f := by
    intro y t f
    funext z
    by_cases hz : z = y
    · subst hz
      simp [shiftBy, Function.update_self]
    · simp [shiftBy, Function.update_of_ne hz]
  -- off the training set the score has zero total
  have hzero : ∀ y : X, y ∉ T →
      (∑ f : X → ZMod k, (if L f y = f y then ((k : ℚ) - 1) else -1)) = 0 := by
    intro y hy
    have hagree : ∀ (t : ZMod k) (f : X → ZMod k), L (shiftBy y t f) = L f := by
      intro t f
      refine hL _ _ (fun z hz => ?_)
      have hzy : z ≠ y := fun h => hy (h ▸ hz)
      simp [shiftBy, Function.update_of_ne hzy]
    have hval : ∀ (t : ZMod k) (f : X → ZMod k), (shiftBy y t f) y = f y + t := by
      intro t f
      simp [shiftBy, Function.update_self]
    have hEq : ∀ t : ZMod k,
        (∑ f : X → ZMod k, (if L f y = f y then ((k : ℚ) - 1) else -1))
          = ∑ f : X → ZMod k, (if L f y = f y + t then ((k : ℚ) - 1) else -1) := by
      intro t
      let e : (X → ZMod k) ≃ (X → ZMod k) :=
        { toFun := shiftBy y t, invFun := shiftBy y (-t),
          left_inv := hsi y t,
          right_inv := by
            intro f
            have := hsi y (-t) f
            simpa using this }
      calc (∑ f : X → ZMod k, (if L f y = f y then ((k : ℚ) - 1) else -1))
          = ∑ f : X → ZMod k, (if L (e f) y = (e f) y then ((k : ℚ) - 1) else -1) :=
            (Equiv.sum_comp e (fun f => if L f y = f y then ((k : ℚ) - 1) else -1)).symm
        _ = ∑ f : X → ZMod k, (if L f y = f y + t then ((k : ℚ) - 1) else -1) := by
            refine Finset.sum_congr rfl (fun f _ => ?_)
            show (if L (shiftBy y t f) y = (shiftBy y t f) y then ((k : ℚ) - 1) else -1)
              = (if L f y = f y + t then ((k : ℚ) - 1) else -1)
            rw [hagree t f, hval t f]
    have hinner : ∀ f : X → ZMod k,
        (∑ t : ZMod k, (if L f y = f y + t then ((k : ℚ) - 1) else -1)) = 0 := by
      intro f
      have hiff : ∀ t : ZMod k, (L f y = f y + t) ↔ (t = L f y - f y) := by
        intro t
        constructor
        · intro h; rw [h]; ring
        · intro h; rw [h]; ring
      have hsplit : ∀ t : ZMod k, (if L f y = f y + t then ((k : ℚ) - 1) else -1)
          = -1 + (if t = L f y - f y then (k : ℚ) else 0) := by
        intro t
        rw [if_congr (hiff t) rfl rfl]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun t _ => hsplit t), Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
        Finset.sum_ite_eq' Finset.univ (L f y - f y) (fun _ => (k : ℚ))]
      simp
    have hktotal : (k : ℚ) * (∑ f : X → ZMod k, (if L f y = f y then ((k : ℚ) - 1) else -1)) = 0 := by
      calc (k : ℚ) * (∑ f : X → ZMod k, (if L f y = f y then ((k : ℚ) - 1) else -1))
          = ∑ _t : ZMod k, (∑ f : X → ZMod k, (if L f y = f y then ((k : ℚ) - 1) else -1)) := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        _ = ∑ t : ZMod k, ∑ f : X → ZMod k, (if L f y = f y + t then ((k : ℚ) - 1) else -1) :=
            Finset.sum_congr rfl (fun t _ => hEq t)
        _ = ∑ f : X → ZMod k, ∑ t : ZMod k, (if L f y = f y + t then ((k : ℚ) - 1) else -1) :=
            Finset.sum_comm
        _ = 0 := by
            rw [Finset.sum_congr rfl (fun f _ => hinner f)]
            simp
    have := mul_eq_zero.mp hktotal
    rcases this with h | h
    · exact absurd h hkQ
    · exact h
  -- on the training set every score is `k - 1`
  have hcert : ∀ y : X, y ∈ T →
      (∑ f : X → ZMod k, (if L f y = f y then ((k : ℚ) - 1) else -1))
        = ((k : ℚ) - 1) * (Fintype.card (X → ZMod k) : ℚ) := by
    intro y hy
    have hone : ∀ f : X → ZMod k,
        (if L f y = f y then ((k : ℚ) - 1) else -1) = (k : ℚ) - 1 := by
      intro f
      rw [if_pos (hT f y hy)]
    rw [Finset.sum_congr rfl (fun f _ => hone f), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  unfold E
  rw [Finset.sum_comm]
  have hrow : ∀ y : X, (∑ f : X → ZMod k, (if L f y = f y then ((k : ℚ) - 1) else -1))
      = (if y ∈ T then ((k : ℚ) - 1) * (Fintype.card (X → ZMod k) : ℚ) else 0) := by
    intro y
    by_cases hy : y ∈ T
    · rw [if_pos hy, hcert y hy]
    · rw [if_neg hy, hzero y hy]
  rw [Finset.sum_congr rfl (fun y _ => hrow y), Finset.sum_ite, Finset.sum_const,
    Finset.sum_const, Finset.filter_mem_eq_inter, Finset.univ_inter, nsmul_eq_mul,
    nsmul_eq_mul]
  field_simp
  ring
