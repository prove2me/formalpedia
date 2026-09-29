-- Prove2me | solution 1 for mme_dwz_table2_affine_hash_incidence_factory
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:38:18.788772+00:00
-- url     : https://prove2.me/submissions/c6e61a5d-e24a-4296-b22f-d88042cac022

import Definitions.Def_mme_dwz_asymmetric_affine_hash
import Theorems.Thm_mme_dwz_asymmetric_hash_singleton_fiber_card
import Theorems.Thm_mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
import Theorems.Thm_mme_dwz_table2_component_words_affine_hash_adapter
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
import Theorems.Thm_mme_lower_half_ZMod_image_card

set_option autoImplicit false
set_option warningAsError true

open MME

private def table2CastX {p N : ℕ}
    (w : Fin (N + 1) → Fin 15) : Fin (N + 1) → ZMod p := fun t ↦
  (MME.DWZSquare.shapeX (w t)).val

private def table2CastY {p N : ℕ}
    (w : Fin (N + 1) → Fin 15) : Fin (N + 1) → ZMod p := fun t ↦
  (MME.DWZSquare.shapeY (w t)).val

private def table2CastZ {p N : ℕ}
    (w : Fin (N + 1) → Fin 15) : Fin (N + 1) → ZMod p := fun t ↦
  (MME.DWZSquare.shapeZ (w t)).val

theorem solution
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p) (hp5 : 5 ≤ p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A T : Finset (Fin (N + 1) → Fin 15)) (hTA : T ⊆ A) :
    let Edge := Fin (N + 1) → Fin 15
    let XWord := Fin (N + 1) → Fin 5
    let x : Edge → XWord := fun w t ↦ MME.DWZSquare.shapeX (w t)
    let y : Edge → XWord := fun w t ↦ MME.DWZSquare.shapeY (w t)
    let Ω := (Fin (N + 2) → ZMod p) × ZMod p
    Fintype.card Ω = p ^ (N + 3) ∧
      ∃ E : Ω → Finset Edge,
        (∀ q, E q ⊆ A) ∧
        (∀ a ∈ T,
          (Finset.univ.filter (fun q : Ω ↦ a ∈ E q)).card =
            S.card * p ^ (N + 1)) ∧
        ∀ ab ∈ (T.product A).filter (fun ab ↦
            ab.1 ≠ ab.2 ∧ (x ab.1 = x ab.2 ∨ y ab.1 = y ab.2)),
          (Finset.univ.filter (fun q : Ω ↦
            ab.1 ∈ E q ∧ ab.2 ∈ E q)).card ≤
              S.card * p ^ N := by
  classical
  dsimp only
  let castS : Finset (ZMod p) :=
    S.image (fun a : ℕ ↦ (a : ZMod p))
  let E : ((Fin (N + 2) → ZMod p) × ZMod p) →
      Finset (Fin (N + 1) → Fin 15) := fun q ↦
    A.filter (fun w ↦
      let ω := dwzAsymmetricHashStateOfAffine q
      dwzAsymmetricHashX ω (table2CastX w) ∈ castS ∧
        dwzAsymmetricHashY ω (table2CastY w) ∈ castS ∧
        dwzAsymmetricHashZ (4 : ZMod p) ω (table2CastZ w) ∈ castS)
  have hsupport (w : Fin (N + 1) → Fin 15) (t : Fin (N + 1)) :
      table2CastX (p := p) w t + table2CastY w t + table2CastZ w t =
        (4 : ZMod p) := by
    have hsum := MME.DWZSquare.shape_sum (w t)
    have hcast := congrArg (fun n : ℕ ↦ (n : ZMod p)) hsum
    simpa only [table2CastX, table2CastY, table2CastZ,
      Nat.cast_add, Nat.cast_ofNat] using hcast
  have hcastCard : castS.card = S.card := by
    exact mme_lower_half_ZMod_image_card p S hSrange
  have hE : ∀ q, E q ⊆ A := by
    intro q w hw
    exact (Finset.mem_filter.mp hw).1
  have hsingle : ∀ a ∈ T,
      (Finset.univ.filter (fun q :
          (Fin (N + 2) → ZMod p) × ZMod p ↦ a ∈ E q)).card =
        S.card * p ^ (N + 1) := by
    intro a haT
    have haA : a ∈ A := hTA haT
    have hsets :
        Finset.univ.filter (fun q :
            (Fin (N + 2) → ZMod p) × ZMod p ↦ a ∈ E q) =
          dwzAsymmetricAffineStatesRetaining (4 : ZMod p) castS
            (table2CastX a) (table2CastY a) (table2CastZ a) := by
      ext q
      simp only [E, dwzAsymmetricAffineStatesRetaining,
        Finset.mem_filter, Finset.mem_univ, true_and, haA]
      exact mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
        hpodd S hSrange hSfree (4 : ZMod p)
          (table2CastX a) (table2CastY a) (table2CastZ a)
          (hsupport a) q
    rw [hsets, mme_dwz_asymmetric_hash_singleton_fiber_card
      hpodd (4 : ZMod p) castS (table2CastX a)
        (table2CastY a) (table2CastZ a) (hsupport a), hcastCard]
  have hpair : ∀ ab ∈ (T.product A).filter (fun ab ↦
      ab.1 ≠ ab.2 ∧
        ((fun t ↦ MME.DWZSquare.shapeX (ab.1 t)) =
            (fun t ↦ MME.DWZSquare.shapeX (ab.2 t)) ∨
          (fun t ↦ MME.DWZSquare.shapeY (ab.1 t)) =
            (fun t ↦ MME.DWZSquare.shapeY (ab.2 t)))),
      (Finset.univ.filter (fun q :
          (Fin (N + 2) → ZMod p) × ZMod p ↦
        ab.1 ∈ E q ∧ ab.2 ∈ E q)).card ≤
          S.card * p ^ N := by
    intro ab hab
    have hab' := Finset.mem_filter.mp hab
    have hprod := Finset.mem_product.mp hab'.1
    have haT : ab.1 ∈ T := hprod.1
    have hbA : ab.2 ∈ A := hprod.2
    have haA : ab.1 ∈ A := hTA haT
    have hne : ab.1 ≠ ab.2 := hab'.2.1
    have hshare := hab'.2.2
    have hadapter := mme_dwz_table2_component_words_affine_hash_adapter
      hp5 ab.1 ab.2 hne hshare
    dsimp only at hadapter
    have hsets :
        Finset.univ.filter (fun q :
            (Fin (N + 2) → ZMod p) × ZMod p ↦
          ab.1 ∈ E q ∧ ab.2 ∈ E q) =
          (dwzAsymmetricAffineStatesRetaining (4 : ZMod p) castS
              (table2CastX ab.1) (table2CastY ab.1)
              (table2CastZ ab.1)) ∩
            (dwzAsymmetricAffineStatesRetaining (4 : ZMod p) castS
              (table2CastX ab.2) (table2CastY ab.2)
              (table2CastZ ab.2)) := by
      ext q
      simp only [E, dwzAsymmetricAffineStatesRetaining,
        Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_inter, haA, hbA]
      exact and_congr
        (mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
          hpodd S hSrange hSfree (4 : ZMod p)
            (table2CastX ab.1) (table2CastY ab.1) (table2CastZ ab.1)
            hadapter.1 q)
        (mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
          hpodd S hSrange hSfree (4 : ZMod p)
            (table2CastX ab.2) (table2CastY ab.2) (table2CastZ ab.2)
            hadapter.2.1 q)
    rw [hsets]
    have hbound := mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
      (4 : ZMod p) castS
        (table2CastX ab.1) (table2CastY ab.1) (table2CastZ ab.1)
        (table2CastX ab.2) (table2CastY ab.2) (table2CastZ ab.2)
        hadapter.2.2
    simpa only [hcastCard] using hbound
  refine ⟨?_, E, hE, hsingle, hpair⟩
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    ZMod.card]
  ring

