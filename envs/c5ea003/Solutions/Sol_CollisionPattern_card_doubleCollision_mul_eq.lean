-- Prove2me | solution 1 for CollisionPattern.card_doubleCollision_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T06:06:02.369987+00:00
-- url     : https://prove2.me/submissions/684be965-98e5-4b39-9f1b-2a0e7525fc09

import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_CollisionPatternMarginal
open CollisionPattern AlmostLossless Finset in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ} {p q r : ι} (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    M ^ 2 * ((collisionEvent M p r) ∩ (collisionEvent M q r)).card
      = M ^ Fintype.card ι := by
  classical
  -- a doubly colliding codebook is determined by its values off `{p, q}`
  let e : {H : ι → Fin M // H p = H r ∧ H q = H r} ≃ ({i : ι // i ≠ p ∧ i ≠ q} → Fin M) :=
    { toFun := fun H i => H.1 i
      invFun := fun g => ⟨fun i => if h : i ≠ p ∧ i ≠ q then g ⟨i, h⟩
          else g ⟨r, hpr.symm, hqr.symm⟩, by
          constructor
          · show (if h : p ≠ p ∧ p ≠ q then g ⟨p, h⟩ else g ⟨r, hpr.symm, hqr.symm⟩)
              = (if h : r ≠ p ∧ r ≠ q then g ⟨r, h⟩ else g ⟨r, hpr.symm, hqr.symm⟩)
            rw [dif_neg (by simp), dif_pos ⟨hpr.symm, hqr.symm⟩]
          · show (if h : q ≠ p ∧ q ≠ q then g ⟨q, h⟩ else g ⟨r, hpr.symm, hqr.symm⟩)
              = (if h : r ≠ p ∧ r ≠ q then g ⟨r, h⟩ else g ⟨r, hpr.symm, hqr.symm⟩)
            rw [dif_neg (by simp), dif_pos ⟨hpr.symm, hqr.symm⟩]⟩
      left_inv := fun H => by
        apply Subtype.ext
        funext i
        by_cases h : i ≠ p ∧ i ≠ q
        · simp only [dif_pos h]
        · simp only [dif_neg h]
          by_cases hip : i = p
          · rw [hip, H.2.1]
          · have hiq : i = q := by tauto
            rw [hiq, H.2.2]
      right_inv := fun g => by
        funext i
        simp only [dif_pos i.2] }
  have hcard : ((collisionEvent M p r) ∩ (collisionEvent M q r)).card
      = M ^ (Fintype.card ι - 2) := by
    have h1 : (collisionEvent M p r) ∩ (collisionEvent M q r)
        = univ.filter (fun H : ι → Fin M => H p = H r ∧ H q = H r) := by
      ext H
      simp [collisionEvent]
    rw [h1, ← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]
    congr 1
    rw [Fintype.card_subtype]
    have h2 : univ.filter (fun i : ι => i ≠ p ∧ i ≠ q) = univ \ {p, q} := by
      ext i
      simp
    rw [h2, card_sdiff_of_subset (subset_univ _), card_univ, card_pair hpq]
  have h3 : 3 ≤ Fintype.card ι := by
    have : ({p, q, r} : Finset ι).card = 3 := by
      rw [card_insert_of_notMem (by simp [hpq, hpr]), card_pair hqr]
    rw [← this]
    exact card_le_univ _
  rw [hcard, ← pow_add]
  congr 1
  omega
