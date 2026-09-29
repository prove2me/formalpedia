-- Prove2me | solution 1 for mme_rectangular_MM_support_diagonal_block_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T23:58:00.273942+00:00
-- url     : https://prove2.me/submissions/e9e08fa5-cf87-4b5a-8a99-21ffb013904a

import Theorems.Thm_mme_MM_support_behrend_induced_matching
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false
set_option warningAsError true

private theorem realize_image
    {I X Y Z : Type} [Fintype I] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (edge : I → X × Y × Z)
    (hxy : Function.Injective (fun i ↦ ((edge i).1, (edge i).2.1)))
    (hyz : Function.Injective (fun i ↦ ((edge i).2.1, (edge i).2.2)))
    (hzx : Function.Injective (fun i ↦ ((edge i).2.2, (edge i).1)))
    (hinduced : ∀ x y z : I,
      (edge x).2.1 = (edge y).2.1 →
      (edge y).2.2 = (edge z).2.2 →
      (edge z).1 = (edge x).1 → x = y ∧ y = z) :
    ∃ E : Finset (X × Y × Z),
      Function.Injective (fun e : E ↦ (e.1.1, e.1.2.1)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.1, e.1.2.2)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.2, e.1.1)) ∧
      (∀ x y z : E, x.1.2.1 = y.1.2.1 → y.1.2.2 = z.1.2.2 →
        z.1.1 = x.1.1 → x = y ∧ y = z) ∧
      E.card = Fintype.card I := by
  classical
  let E := Finset.univ.image edge
  have preimage : ∀ e : E, ∃ i, edge i = e.1 := by
    intro e
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp e.2
    exact ⟨i, hi⟩
  refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y h
    obtain ⟨i, hi⟩ := preimage x
    obtain ⟨j, hj⟩ := preimage y
    apply Subtype.ext
    rw [← hi, ← hj]
    exact congrArg edge (hxy (by simpa only [hi, hj] using h))
  · intro x y h
    obtain ⟨i, hi⟩ := preimage x
    obtain ⟨j, hj⟩ := preimage y
    apply Subtype.ext
    rw [← hi, ← hj]
    exact congrArg edge (hyz (by simpa only [hi, hj] using h))
  · intro x y h
    obtain ⟨i, hi⟩ := preimage x
    obtain ⟨j, hj⟩ := preimage y
    apply Subtype.ext
    rw [← hi, ← hj]
    exact congrArg edge (hzx (by simpa only [hi, hj] using h))
  · intro x y z hxy hyz hzx
    obtain ⟨i, hi⟩ := preimage x
    obtain ⟨j, hj⟩ := preimage y
    obtain ⟨k, hk⟩ := preimage z
    obtain ⟨hij, hjk⟩ := hinduced i j k
      (by simpa only [hi, hj] using hxy)
      (by simpa only [hj, hk] using hyz)
      (by simpa only [hk, hi] using hzx)
    constructor
    · exact Subtype.ext (hi.symm.trans ((congrArg edge hij).trans hj))
    · exact Subtype.ext (hj.symm.trans ((congrArg edge hjk).trans hk))
  · rw [Finset.card_image_of_injective _ (by
      intro i j h
      exact hxy (congrArg (fun e : X × Y × Z ↦ (e.1, e.2.1)) h))]
    exact Finset.card_univ

/-- Replicate a square support matching in disjoint diagonal blocks of two
larger alphabets; retain the actual inducedness, not only a scalar count. -/
theorem solution (H B V W : ℕ) (hH : 0 < H)
    (hV : B * H ≤ V) (hW : B * H ≤ W) :
    ∃ E : Finset (Fin H × Fin V × Fin W),
      Function.Injective (fun e : E ↦ (e.1.1, e.1.2.1)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.1, e.1.2.2)) ∧
      Function.Injective (fun e : E ↦ (e.1.2.2, e.1.1)) ∧
      (∀ x y z : E, x.1.2.1 = y.1.2.1 → y.1.2.2 = z.1.2.2 →
        z.1.1 = x.1.1 → x = y ∧ y = z) ∧
      (B : ℝ) * (H : ℝ) ^ 2 *
          Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) ≤
        (E.card : ℝ) := by
  classical
  obtain ⟨S, hsxy, hsyz, hszx, hsinduced, hcard⟩ :=
    mme_MM_support_behrend_induced_matching H hH
  let fy : Fin B × Fin H → Fin V := fun p ↦ Fin.castLE hV (finProdFinEquiv p)
  let fz : Fin B × Fin H → Fin W := fun p ↦ Fin.castLE hW (finProdFinEquiv p)
  have hfy : Function.Injective fy :=
    (Fin.castLE_injective hV).comp finProdFinEquiv.injective
  have hfz : Function.Injective fz :=
    (Fin.castLE_injective hW).comp finProdFinEquiv.injective
  let edge : Fin B × S → Fin H × Fin V × Fin W := fun p ↦
    (p.2.1.1, fy (p.1, p.2.1.2.1), fz (p.1, p.2.1.2.2))
  have hxy : Function.Injective (fun i ↦ ((edge i).1, (edge i).2.1)) := by
    intro i j h
    have hy := hfy (congrArg Prod.snd h)
    exact Prod.ext (congrArg (fun t : Fin B × Fin H ↦ t.1) hy)
      (hsxy (Prod.ext
        (congrArg (fun t : Fin H × Fin V ↦ t.1) h)
        (congrArg (fun t : Fin B × Fin H ↦ t.2) hy)))
  have hyz : Function.Injective (fun i ↦ ((edge i).2.1, (edge i).2.2)) := by
    intro i j h
    have hy := hfy (congrArg Prod.fst h)
    have hz := hfz (congrArg Prod.snd h)
    exact Prod.ext (congrArg (fun t : Fin B × Fin H ↦ t.1) hy)
      (hsyz (Prod.ext
        (congrArg (fun t : Fin B × Fin H ↦ t.2) hy)
        (congrArg (fun t : Fin B × Fin H ↦ t.2) hz)))
  have hzx : Function.Injective (fun i ↦ ((edge i).2.2, (edge i).1)) := by
    intro i j h
    have hz := hfz (congrArg Prod.fst h)
    exact Prod.ext (congrArg (fun t : Fin B × Fin H ↦ t.1) hz)
      (hszx (Prod.ext
        (congrArg (fun t : Fin B × Fin H ↦ t.2) hz)
        (congrArg (fun t : Fin W × Fin H ↦ t.2) h)))
  obtain ⟨E, hexy, heyz, hezx, heinduced, hecard⟩ := realize_image edge hxy hyz hzx (by
    intro i j k hy hz hx
    have hy' := hfy hy
    have hz' := hfz hz
    obtain ⟨hij, hjk⟩ := hsinduced i.2 j.2 k.2
      (congrArg (fun t : Fin B × Fin H ↦ t.2) hy')
      (congrArg (fun t : Fin B × Fin H ↦ t.2) hz') hx
    exact ⟨Prod.ext (congrArg (fun t : Fin B × Fin H ↦ t.1) hy') hij,
      Prod.ext (congrArg (fun t : Fin B × Fin H ↦ t.1) hz') hjk⟩)
  refine ⟨E, hexy, heyz, hezx, heinduced, ?_⟩
  have hcount : E.card = B * S.card := by simpa using hecard
  rw [hcount, Nat.cast_mul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg B)
