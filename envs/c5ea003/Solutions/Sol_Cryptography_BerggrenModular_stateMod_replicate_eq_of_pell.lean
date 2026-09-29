-- Prove2me | solution 1 for Cryptography.BerggrenModular.stateMod_replicate_eq_of_pell
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T18:36:43.677299+00:00
-- url     : https://prove2.me/submissions/4bde82cb-3928-4b72-89c2-556c364c6a04

import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_Hardness
import Definitions.Def_Cryptography_BerggrenModular_Modular
import Definitions.Def_Cryptography_BerggrenModular_SilverOrbit
import Definitions.Def_Cryptography_BerggrenModular_Threshold
open Cryptography BerggrenModular in
theorem solution {m : ℕ} [NeZero m] (hm : Odd m) {t₁ t₂ : ℕ}
    (hpar : t₁ % 2 = t₂ % 2)
    (hs : ((pellS t₁ : ℤ) : ZMod m) = ((pellS t₂ : ℤ) : ZMod m))
    (hc : ((pellC t₁ : ℤ) : ZMod m) = ((pellC t₂ : ℤ) : ZMod m)) :
    stateMod m (List.replicate t₁ Move.m2) = stateMod m (List.replicate t₂ Move.m2) := by
  have hleg : ∀ t : ℕ, (orbit2 t).2.1 - (orbit2 t).1 = (-1) ^ t := by
    intro t
    induction t with
    | zero => simp [orbit2, applyWord, root]
    | succ t ih =>
      have e : orbit2 (t + 1) = applyMove Move.m2 (orbit2 t) := rfl
      rw [e, pow_succ, ← ih]
      simp only [applyMove]
      ring
  have hsgn : ((-1 : ℤ) ^ t₁) = (-1) ^ t₂ := by
    rw [neg_one_pow_eq_pow_mod_two, hpar, ← neg_one_pow_eq_pow_mod_two]
  have h2 : IsUnit (2 : ZMod m) := by
    have := (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hm)).isUnit
    rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this
  have ha : ∀ t : ℕ, (2 : ZMod m) * (((orbit2 t).1 : ℤ) : ZMod m) =
      ((pellS t : ℤ) : ZMod m) - (((-1 : ℤ) ^ t : ℤ) : ZMod m) := by
    intro t
    rw [← hleg t]
    simp only [pellS]
    push_cast
    ring
  have hb : ∀ t : ℕ, (2 : ZMod m) * (((orbit2 t).2.1 : ℤ) : ZMod m) =
      ((pellS t : ℤ) : ZMod m) + (((-1 : ℤ) ^ t : ℤ) : ZMod m) := by
    intro t
    rw [← hleg t]
    simp only [pellS]
    push_cast
    ring
  show redTri m (orbit2 t₁) = redTri m (orbit2 t₂)
  simp only [redTri, Prod.mk.injEq]
  refine ⟨h2.mul_left_cancel ?_, h2.mul_left_cancel ?_, hc⟩
  · rw [ha, ha, hs, hsgn]
  · rw [hb, hb, hs, hsgn]
