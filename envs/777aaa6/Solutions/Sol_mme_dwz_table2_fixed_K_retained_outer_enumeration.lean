-- Prove2me | solution 1 for mme_dwz_table2_fixed_K_retained_outer_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T09:36:58.051071+00:00
-- url     : https://prove2.me/submissions/544be162-1bad-487b-a842-26a79559a314

import Theorems.Thm_mme_dwz_table2_fixed_K_retained_finset_outer_image

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

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
      ∃ outer : Fin I.card → Outer,
        Function.Injective outer ∧
        (∀ a ∈ I, ∃ j : Fin I.card,
          (outer j).1 = fun t ↦ a (reindex.symm t)) ∧
        ∀ j : Fin I.card, ∃ a ∈ I,
          (outer j).1 = fun t ↦ a (reindex.symm t) := by
  classical
  dsimp only
  intro I hI
  obtain ⟨J, hcard, hforward, hbackward⟩ :=
    mme_dwz_table2_fixed_K_retained_finset_outer_image m hm K I hI
  let eFin : Fin I.card ≃ Fin J.card := finCongr hcard.symm
  let eJ : Fin I.card ≃ {w // w ∈ J} := eFin.trans J.equivFin.symm
  let outer : Fin I.card → _ := fun j ↦ (eJ j).1
  refine ⟨outer, ?_, ?_, ?_⟩
  · intro j j' hj
    apply eJ.injective
    apply Subtype.ext
    exact hj
  · intro a ha
    obtain ⟨w, hwJ, hw⟩ := hforward a ha
    let wJ : {w // w ∈ J} := ⟨w, hwJ⟩
    refine ⟨eJ.symm wJ, ?_⟩
    simpa only [outer, Equiv.apply_symm_apply] using hw
  · intro j
    obtain ⟨a, haI, ha⟩ := hbackward (outer j) (eJ j).2
    exact ⟨a, haI, ha⟩
