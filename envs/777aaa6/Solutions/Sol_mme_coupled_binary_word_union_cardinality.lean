-- Prove2me | solution 1 for mme_coupled_binary_word_union_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T04:06:14.525782+00:00
-- url     : https://prove2.me/submissions/7361ec78-c1b1-411d-9e84-96192b9d0913

import Definitions.Def_mme_kron_pow_word_reindex
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Basic

open MME.DWZComponentRestriction BigOperators
universe u
set_option autoImplicit false

private theorem numericLetterFiber_card (q : ℕ) (b : Fin 3)
    (hb : b = 0 ∨ b = 1) :
    Fintype.card {x : ULift.{u} (Fin q ⊕ Fin q) //
      Sum.elim (fun _ ↦ (0 : Fin 3)) (fun _ ↦ 1) x.down = b} = q := by
  classical
  let grade : ULift.{u} (Fin q ⊕ Fin q) → Fin 3 :=
    fun x ↦ Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) x.down
  let e : {x : ULift.{u} (Fin q ⊕ Fin q) // grade x = b} ≃ Fin q :=
    { toFun := fun x ↦ Sum.elim id id x.val.down
      invFun := fun i ↦ ⟨⟨if b = 0 then Sum.inl i else Sum.inr i⟩, by
        rcases hb with rfl | rfl <;> simp [grade]⟩
      left_inv := by
        rintro ⟨⟨x⟩, hx⟩
        apply Subtype.ext
        cases x with
        | inl i =>
          have h : b = 0 := hx.symm
          simp [h]
        | inr i =>
          have h : b = 1 := hx.symm
          simp [h]
      right_inv := by
        intro i
        rcases hb with rfl | rfl <;> simp }
  exact (Fintype.card_congr e).trans (Fintype.card_fin q)

/-- Every prescribed binary grade word has exactly one independent numeric
label at each position, hence exactly `q ^ N` lifted recursive words. -/
theorem mme_coupled_binary_word_fiber_cardinality (q N : ℕ)
    (b : Fin N → Fin 3) (hb : ∀ r, b r = 0 ∨ b r = 1) :
    Fintype.card {w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N //
      ∀ r, Sum.elim (fun _ ↦ (0 : Fin 3)) (fun _ ↦ 1)
        (PowIndex.get N w r).down = b r} = q ^ N := by
  classical
  let grade : ULift.{u} (Fin q ⊕ Fin q) → Fin 3 :=
    fun x ↦ Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) x.down
  let e := Equiv.subtypeEquivOfSubtype
    (p := fun w : Fin N → ULift.{u} (Fin q ⊕ Fin q) ↦ ∀ r, grade (w r) = b r)
    (PowIndex.equivFun (ULift.{u} (Fin q ⊕ Fin q)) N)
  calc
    _ = Fintype.card (∀ r : Fin N,
        {x : ULift.{u} (Fin q ⊕ Fin q) // grade x = b r}) :=
      Fintype.card_congr (e.trans (Equiv.subtypePiEquivPi (p := fun r x ↦ grade x = b r)))
    _ = ∏ r : Fin N, Fintype.card
        {x : ULift.{u} (Fin q ⊕ Fin q) // grade x = b r} := Fintype.card_pi
    _ = ∏ _r : Fin N, q := by
      apply Finset.prod_congr rfl
      intro r _
      exact numericLetterFiber_card q (b r) (hb r)
    _ = q ^ N := by simp


/-- A union of distinct binary grade patterns has `q ^ N` numeric words per
pattern. Counting the pattern set avoids counting repeated labels twice. -/
theorem solution (q N : ℕ)
    (patterns : Finset (Fin N → Fin 3))
    (hbinary : ∀ b ∈ patterns, ∀ r, b r = 0 ∨ b r = 1) :
    Fintype.card {w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N //
      (fun r ↦ Sum.elim (fun _ ↦ (0 : Fin 3)) (fun _ ↦ 1)
        (PowIndex.get N w r).down) ∈ patterns} = patterns.card * q ^ N := by
  classical
  let gradeWord := fun w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N ↦
    fun r ↦ Sum.elim (fun _ ↦ (0 : Fin 3)) (fun _ ↦ 1)
      (PowIndex.get N w r).down
  let e : {w // gradeWord w ∈ patterns} ≃
      (Σ b : {b // b ∈ patterns}, {w // gradeWord w = b.val}) :=
    { toFun := fun w ↦ ⟨⟨gradeWord w.val, w.property⟩, ⟨w.val, rfl⟩⟩
      invFun := fun v ↦ ⟨v.2.val, v.2.property.symm ▸ v.1.property⟩
      left_inv := by intro w; rfl
      right_inv := by
        rintro ⟨⟨b,hb⟩,⟨w,hw⟩⟩
        cases hw
        rfl }
  calc
    _ = ∑ b : {b // b ∈ patterns}, Fintype.card {w // gradeWord w = b.val} :=
      (Fintype.card_congr e).trans Fintype.card_sigma
    _ = ∑ _b : {b // b ∈ patterns}, q ^ N := by
      apply Finset.sum_congr rfl
      intro b _
      have he : {w // gradeWord w = b.val} ≃
          {w // ∀ r, gradeWord w r = b.val r} :=
        Equiv.subtypeEquivRight (fun _ ↦ funext_iff)
      exact (Fintype.card_congr he).trans
        (mme_coupled_binary_word_fiber_cardinality q N b.val
          (hbinary b.val b.property))
    _ = patterns.card * q ^ N := by simp

#print axioms solution
