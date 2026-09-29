-- Prove2me | solution 1 for mme_dwz_table2_fixed_K_retained_finset_outer_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T09:06:53.566379+00:00
-- url     : https://prove2.me/submissions/f9b8f10f-470a-4fc7-ab14-668719a2530b

import Theorems.Thm_mme_dwz_table2_fixed_K_reindexed_target_equiv_outer

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

/-- Every retained subfamily of the fixed-`K` first-hash target has a coherent
literal `Outer` image of exactly the same cardinality.  This is the family-
level transport needed to index the Claim-6.8 broken copies, not merely a
pointwise existence statement. -/
theorem solution
    (m : ℕ) (hm : 0 < m)
    (K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5) :
    let L := MME.DWZTable2Counts.scale * m
    let N := L - 1
    let reindex : Fin (N + 1) ≃ Fin L := finCongr (by
      dsimp only [N, L]
      exact Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    let P : (Fin L → Fin 15) → Prop := fun w ↦
      (∀ x, Fintype.card {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
      (∀ y, Fintype.card {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
      ∀ z, Fintype.card {t // MME.DWZSquare.shapeZ (w t) = z} =
        MME.DWZTable2Counts.alphaZ z * m
    let A0 : Finset (Fin L → Fin 15) := Finset.univ.filter P
    let W : (Fin L → Fin 15) ≃ (Fin (N + 1) → Fin 15) :=
      { toFun := fun w t ↦ w (reindex t)
        invFun := fun w t ↦ w (reindex.symm t)
        left_inv := fun w ↦ by funext t; simp
        right_inv := fun w ↦ by funext t; simp }
    let A : Finset (Fin (N + 1) → Fin 15) := A0.map W.toEmbedding
    let FixedK : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
      (∀ t, MME.DWZSquare.shapeZ (a t) = K (reindex t)) ∧
      ∀ s, Fintype.card {t : Fin (N + 1) // a t = s} =
        MME.DWZTable2Counts.component s * m
    let T := A.filter FixedK
    let Outer :=
      {w : Fin L → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
        ∀ s, Fintype.card {t : Fin L // w t = s} =
          MME.DWZTable2Counts.component s * m}
    ∀ I : Finset (Fin (N + 1) → Fin 15), I ⊆ T →
      ∃ J : Finset Outer,
        J.card = I.card ∧
        (∀ a ∈ I, ∃ w ∈ J,
          w.1 = fun t ↦ a (reindex.symm t)) ∧
        ∀ w ∈ J, ∃ a ∈ I,
          w.1 = fun t ↦ a (reindex.symm t) := by
  classical
  let L := MME.DWZTable2Counts.scale * m
  let N := L - 1
  have hL : N + 1 = L := by
    dsimp only [N, L]
    exact Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm)))
  let reindex : Fin (N + 1) ≃ Fin L := finCongr hL
  let alphaX : Fin 5 → ℕ := fun x ↦
    ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
      MME.DWZTable2Counts.component s.1 * m
  let alphaY : Fin 5 → ℕ := fun y ↦
    ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
      MME.DWZTable2Counts.component s.1 * m
  let P : (Fin L → Fin 15) → Prop := fun w ↦
    (∀ x, Fintype.card {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
    (∀ y, Fintype.card {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
    ∀ z, Fintype.card {t // MME.DWZSquare.shapeZ (w t) = z} =
      MME.DWZTable2Counts.alphaZ z * m
  let A0 : Finset (Fin L → Fin 15) := Finset.univ.filter P
  let W : (Fin L → Fin 15) ≃ (Fin (N + 1) → Fin 15) :=
    { toFun := fun w t ↦ w (reindex t)
      invFun := fun w t ↦ w (reindex.symm t)
      left_inv := fun w ↦ by funext t; simp
      right_inv := fun w ↦ by funext t; simp }
  let A : Finset (Fin (N + 1) → Fin 15) := A0.map W.toEmbedding
  let FixedK : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
    (∀ t, MME.DWZSquare.shapeZ (a t) = K (reindex t)) ∧
    ∀ s, Fintype.card {t : Fin (N + 1) // a t = s} =
      MME.DWZTable2Counts.component s * m
  let T := A.filter FixedK
  let Outer :=
    {w : Fin L → Fin 15 //
      (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m}
  change ∀ I : Finset (Fin (N + 1) → Fin 15), I ⊆ T →
    ∃ J : Finset Outer,
      J.card = I.card ∧
      (∀ a ∈ I, ∃ w ∈ J,
        w.1 = fun t ↦ a (reindex.symm t)) ∧
      ∀ w ∈ J, ∃ a ∈ I,
        w.1 = fun t ↦ a (reindex.symm t)
  intro I hIT
  have heq := mme_dwz_table2_fixed_K_reindexed_target_equiv_outer m hm K
  change ∃ e : {a : Fin (N + 1) → Fin 15 // a ∈ T} ≃ Outer,
    (∀ a, (e a).1 = fun t ↦ a.1 (reindex.symm t)) ∧
    T.card = Nat.card Outer at heq
  obtain ⟨outerEquiv, houterEquiv, _⟩ := heq
  let inc : {a // a ∈ I} ↪ {a : Fin (N + 1) → Fin 15 // a ∈ T} :=
    { toFun := fun a ↦ ⟨a.1, hIT a.2⟩
      inj' := by
        intro a b h
        apply Subtype.ext
        exact congrArg
          (fun x : {a : Fin (N + 1) → Fin 15 // a ∈ T} ↦ x.1) h }
  let g : {a // a ∈ I} ↪ Outer :=
    { toFun := fun a ↦ outerEquiv (inc a)
      inj' := fun a b h ↦ inc.injective (outerEquiv.injective h) }
  let J : Finset _ := I.attach.map g
  refine ⟨J, ?_, ?_, ?_⟩
  · simp only [J, Finset.card_map, Finset.card_attach]
  · intro a ha
    let aa : {a // a ∈ I} := ⟨a, ha⟩
    refine ⟨g aa, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨aa, by simp, rfl⟩
    · exact houterEquiv (inc aa)
  · intro w hw
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hw
    refine ⟨a.1, a.2, ?_⟩
    exact houterEquiv (inc a)

