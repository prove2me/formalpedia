-- Prove2me | solution 1 for mme_dwz_q6_common_halving_union_matrix_pattern_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T04:17:42.713298+00:00
-- url     : https://prove2.me/submissions/8a471f7e-b13c-41fb-83bb-8d65925135d7

import Theorems.Thm_mme_dwz_q6_common_halving_union_matrix_cardinality_restriction
import Theorems.Thm_mme_coupled_binary_word_union_cardinality
import Definitions.Def_mme_kron_pow_word_reindex
import Mathlib.Logic.Equiv.Fin.Basic

open MME MME.DWZComponentRestriction
universe u
set_option autoImplicit false

private def firstTraceLetterEquiv (q : ℕ) :
    ULift.{u} (Fin 1 × Fin (q + q)) ≃ ULift.{u} (Fin q ⊕ Fin q) where
  toFun x := ⟨finSumFinEquiv.symm x.down.2⟩
  invFun x := ⟨(0, finSumFinEquiv x.down)⟩
  left_inv := by
    rintro ⟨i,j⟩
    have hi : i = 0 := Subsingleton.elim _ _
    simp [hi]
  right_inv := by intro x; simp

private def secondTraceLetterEquiv (q : ℕ) :
    ULift.{u} (Fin (q + q) × Fin 1) ≃ ULift.{u} (Fin q ⊕ Fin q) where
  toFun x := ⟨Sum.swap (finSumFinEquiv.symm x.down.1)⟩
  invFun x := ⟨(finSumFinEquiv (Sum.swap x.down), 0)⟩
  left_inv := by
    rintro ⟨i,j⟩
    have hj : j = 0 := Subsingleton.elim _ _
    simp [hj]
  right_inv := by intro x; simp

private def traceWordEquiv {α β : Type u} (N : ℕ) (e : α ≃ β) :
    PowIndex α N ≃ PowIndex β N :=
  (PowIndex.equivFun α N).trans
    ((Equiv.piCongrRight (fun _ : Fin N ↦ e)).trans (PowIndex.equivFun β N).symm)

/-- Inverse trace labels in either orientation preserve the cardinality of
any selected set of coupled words. -/
theorem mme_paired_inverse_trace_word_selection_cardinality (q N : ℕ)
    (keepX keepY : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N → Prop)
    [DecidablePred keepX] [DecidablePred keepY] :
    let h0 := fun w : PowIndex (ULift.{u} (Fin 1 × Fin (q + q))) N ↦
      PowIndex.ofFun N (fun r ↦
        (⟨finSumFinEquiv.symm (PowIndex.get N w r).down.2⟩ : ULift.{u} (Fin q ⊕ Fin q)))
    let h1 := fun w : PowIndex (ULift.{u} (Fin (q + q) × Fin 1)) N ↦
      PowIndex.ofFun N (fun r ↦
        (⟨Sum.swap (finSumFinEquiv.symm (PowIndex.get N w r).down.1)⟩ :
          ULift.{u} (Fin q ⊕ Fin q)))
    Fintype.card {w // keepX (h0 w)} = Fintype.card {w // keepX w} ∧
    Fintype.card {w // keepY (h1 w)} = Fintype.card {w // keepY w} := by
  constructor
  · exact Fintype.card_congr
      (Equiv.subtypeEquivOfSubtype (traceWordEquiv N (firstTraceLetterEquiv q)))
  · exact Fintype.card_congr
      (Equiv.subtypeEquivOfSubtype (traceWordEquiv N (secondTraceLetterEquiv q)))

private theorem binaryFamilyUnion_card (q N : ℕ) {ι : Type} [Fintype ι]
    (pattern : ι → Fin N → Fin 3)
    (hb : ∀ i r, pattern i r = 0 ∨ pattern i r = 1) :
    Fintype.card {w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N //
      ∃ i, ∀ r, Sum.elim (fun _ ↦ (0 : Fin 3)) (fun _ ↦ 1)
        (PowIndex.get N w r).down = pattern i r} =
      (Finset.univ.image pattern).card * q ^ N := by
  classical
  let gradeWord := fun w : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) N ↦
    fun r ↦ Sum.elim (fun _ ↦ (0 : Fin 3)) (fun _ ↦ 1)
      (PowIndex.get N w r).down
  have he : {w // ∃ i, ∀ r, gradeWord w r = pattern i r} ≃
      {w // gradeWord w ∈ Finset.univ.image pattern} :=
    Equiv.subtypeEquivRight (fun w ↦ by simp [funext_iff, eq_comm])
  rw [Fintype.card_congr he]
  apply mme_coupled_binary_word_union_cardinality
  intro b hb' r
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb'
  exact hb i r

/-- The matrix extracted from the two common-halving word unions has one
factor of `6 ^ N` in each dimension, for the independent numeric labels. -/
theorem solution
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    let PX := Finset.univ.image (fun p : Fin A × Fin H ↦
      fun r : Fin N ↦ (family.entry p).val 0 (halving.position (Sum.inl r)))
    let PY := Finset.univ.image (fun p : Fin A × Fin H ↦
      fun r : Fin N ↦ (family.entry p).val 1 (halving.position (Sum.inr r)))
    TensorObj.Restrict (MMObj K (PX.card * 6 ^ N) 1 (PY.card * 6 ^ N))
      (componentPairRestricted K s m) := by
  intro PX PY
  classical
  let x := fun p : Fin A × Fin H ↦
    fun r : Fin N ↦ (family.entry p).val 0 (halving.position (Sum.inl r))
  let y := fun p : Fin A × Fin H ↦
    fun r : Fin N ↦ (family.entry p).val 1 (halving.position (Sum.inr r))
  have bx : ∀ p r, x p r = 0 ∨ x p r = 1 := by
    intro p r
    rcases (family.entry p).property.1 (halving.position (Sum.inl r)) with h | h | h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
    · exact Or.inl h.1
    · exact Or.inr h.1
  have by' : ∀ p r, y p r = 0 ∨ y p r = 1 := by
    intro p r
    rcases (family.entry p).property.1 (halving.position (Sum.inr r)) with h | h | h | h
    · exact Or.inl h.2.1
    · exact Or.inr h.2.1
    · exact Or.inr h.2.1
    · exact Or.inl h.2.1
  let gradeWord := fun w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N ↦
    fun r ↦ Sum.elim (fun _ ↦ (0 : Fin 3)) (fun _ ↦ 1)
      (PowIndex.get N w r).down
  let keepX := fun w ↦ ∃ p, ∀ r, gradeWord w r = x p r
  let keepY := fun w ↦ ∃ p, ∀ r, gradeWord w r = y p r
  letI : DecidablePred keepX := Classical.decPred _
  letI : DecidablePred keepY := Classical.decPred _
  obtain ⟨hx, hy⟩ := mme_paired_inverse_trace_word_selection_cardinality 6 N keepX keepY
  have cx := binaryFamilyUnion_card.{u} 6 N x bx
  have cy := binaryFamilyUnion_card.{u} 6 N y by'
  have h := mme_dwz_q6_common_halving_union_matrix_cardinality_restriction
    (K := K) s hs m hN family halving
  dsimp only at h hx hy
  erw [hx, hy] at h
  simp only [Fintype.card_eq_nat_card] at h cx cy
  rw [cx, cy] at h
  exact h

#print axioms solution
