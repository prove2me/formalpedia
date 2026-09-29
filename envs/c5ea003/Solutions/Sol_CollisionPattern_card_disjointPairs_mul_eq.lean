-- Prove2me | solution 1 for CollisionPattern.card_disjointPairs_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T02:08:13.791808+00:00
-- url     : https://prove2.me/submissions/d4363428-4377-412f-8226-530f20e4fe80

import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_CollisionPatternMarginal
open CollisionPattern AlmostLossless Finset in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ} {p q r s : ι} (hpq : p ≠ q)
    (hrs : r ≠ s) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) :
    M ^ 2 * ((collisionEvent M p q) ∩ (collisionEvent M r s)).card
      = M ^ Fintype.card ι := by
  classical
  -- a codebook with `H p = H q` and `H r = H s` is determined by its values off `{p, r}`
  let e : {H : ι → Fin M // H p = H q ∧ H r = H s} ≃ ({i : ι // i ≠ p ∧ i ≠ r} → Fin M) :=
    { toFun := fun H i => H.1 i
      invFun := fun g => ⟨fun i => if h : i ≠ p ∧ i ≠ r then g ⟨i, h⟩
          else if i = p then g ⟨q, hpq.symm, hqr⟩ else g ⟨s, hps.symm, hrs.symm⟩, by
          constructor
          · show (if h : p ≠ p ∧ p ≠ r then g ⟨p, h⟩
                else if p = p then g ⟨q, hpq.symm, hqr⟩ else g ⟨s, hps.symm, hrs.symm⟩)
              = (if h : q ≠ p ∧ q ≠ r then g ⟨q, h⟩
                else if q = p then g ⟨q, hpq.symm, hqr⟩ else g ⟨s, hps.symm, hrs.symm⟩)
            rw [dif_neg (by simp), if_pos rfl, dif_pos ⟨hpq.symm, hqr⟩]
          · show (if h : r ≠ p ∧ r ≠ r then g ⟨r, h⟩
                else if r = p then g ⟨q, hpq.symm, hqr⟩ else g ⟨s, hps.symm, hrs.symm⟩)
              = (if h : s ≠ p ∧ s ≠ r then g ⟨s, h⟩
                else if s = p then g ⟨q, hpq.symm, hqr⟩ else g ⟨s, hps.symm, hrs.symm⟩)
            rw [dif_neg (by simp), if_neg (fun h => hpr h.symm), dif_pos ⟨hps.symm, hrs.symm⟩]⟩
      left_inv := fun H => by
        apply Subtype.ext
        funext i
        by_cases h : i ≠ p ∧ i ≠ r
        · simp only [dif_pos h]
        · simp only [dif_neg h]
          by_cases hip : i = p
          · rw [if_pos hip, hip, H.2.1]
          · have hir : i = r := by tauto
            rw [if_neg hip, hir, H.2.2]
      right_inv := fun g => by
        funext i
        simp only [dif_pos i.2] }
  have hcard : ((collisionEvent M p q) ∩ (collisionEvent M r s)).card
      = M ^ (Fintype.card ι - 2) := by
    have h1 : (collisionEvent M p q) ∩ (collisionEvent M r s)
        = univ.filter (fun H : ι → Fin M => H p = H q ∧ H r = H s) := by
      ext H
      simp [collisionEvent]
    rw [h1, ← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]
    congr 1
    rw [Fintype.card_subtype]
    have h2 : univ.filter (fun i : ι => i ≠ p ∧ i ≠ r) = univ \ {p, r} := by
      ext i
      simp
    rw [h2, card_sdiff_of_subset (subset_univ _), card_univ, card_pair hpr]
  have h3 : 2 ≤ Fintype.card ι := by
    rw [← card_pair hpr]
    exact card_le_univ _
  rw [hcard, ← pow_add]
  congr 1
  omega
