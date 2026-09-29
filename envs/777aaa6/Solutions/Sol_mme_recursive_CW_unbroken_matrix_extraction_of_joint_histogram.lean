-- Prove2me | solution 1 for mme_recursive_CW_unbroken_matrix_extraction_of_joint_histogram
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T10:17:33.695407+00:00
-- url     : https://prove2.me/submissions/9ba2c673-e315-448c-87d1-5624bc3fdd61

import Theorems.Thm_mme_recursive_cellWord_nonempty_iff_mass_and_grade
import Theorems.Thm_mme_recursive_CW_unbroken_matrix_extraction_of_supported_words

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.ProfiledCW
open scoped Classical

private theorem count_map {P C W V : Type*} [Fintype P] [Fintype W]
    (cell : P → C) (f : P → W) (g : W → V) (c : C) (v : V) :
    count cell (g ∘ f) c v = ∑ w, if g w = v then count cell f c w else 0 := by
  classical
  simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter]
  have pull (w : W) :
      (if g w = v then ∑ p, if cell p = c ∧ f p = w then (1 : ℕ) else 0 else 0) =
      ∑ p, if g w = v then (if cell p = c ∧ f p = w then (1 : ℕ) else 0) else 0 := by
    by_cases h : g w = v <;> simp [h]
  simp_rw [pull]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : cell p = c
  · simp only [h, true_and, Function.comp_apply]
    rw [Finset.sum_eq_single (f p)]
    · simp
    · intro w hw hwp
      simp [Ne.symm hwp]
    · simp
  · simp [h]

/-- An integer coupling with the prescribed marginals realizes jointly supported profile words. -/
theorem supported_words_of_joint_histogram
    {P C : Type*} [Fintype P] {ell : ℕ}
    (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ)
    (joint : C → (Fin 3 → CompleteWord ell) → ℕ)
    (hmass : ∀ c, ∑ v, joint c v = Nat.card {p : P // cell p = c})
    (hmarginal : ∀ i c s, ∑ v, (if v i = s then joint c v else 0) = mu i c s)
    (hgrade : ∀ c v, 0 < joint c v → ∀ i, grade (v i) = shape c i)
    (hsupport : ∀ c v, 0 < joint c v →
      ∀ r, (v 0 r).val + (v 1 r).val + (v 2 r).val = 2) :
    ∃ w : Fin 3 → P → CompleteWord ell,
      (∀ i p, grade (w i p) = shape (cell p) i) ∧
      (∀ i, Useful cell (mu i) (w i)) ∧
      (∀ p r, (w 0 p r).val + (w 1 p r).val + (w 2 p r).val = 2) ∧
      Useful cell joint (fun p i ↦ w i p) := by
  classical
  let gr (v : Fin 3 → CompleteWord ell) : (Fin 3 → ℕ) × Prop :=
    (fun i ↦ grade (v i), ∀ r, (v 0 r).val + (v 1 r).val + (v 2 r).val = 2)
  let sh (c : C) : (Fin 3 → ℕ) × Prop := (shape c, True)
  have hg (c : C) (v : Fin 3 → CompleteWord ell) (hv : 0 < joint c v) :
      gr v = sh c := by
    apply Prod.ext
    · exact funext (hgrade c v hv)
    · exact propext ⟨fun _ ↦ trivial, fun _ ↦ hsupport c v hv⟩
  obtain ⟨f⟩ := (mme_recursive_cellWord_nonempty_iff_mass_and_grade
    cell gr sh joint).2 ⟨hmass, hg⟩
  refine ⟨fun i p ↦ f.val p i, ?_, ?_, ?_, f.property.2⟩
  · intro i p
    exact congrArg (fun t : (Fin 3 → ℕ) × Prop ↦ t.1 i) (f.property.1 p)
  · intro i c s
    have hh := count_map cell f.val (fun v ↦ v i) c s
    have hf (v) : count cell f.val c v = joint c v := f.property.2 c v
    simpa only [hf, hmarginal i c s] using hh
  · intro p
    exact (congrArg Prod.snd (f.property.1 p)).mpr trivial

private theorem histogram_weight_sum {P C W : Type*}
    [Fintype P] [Fintype C] [Fintype W]
    (cell : P → C) (f : P → W) (weight : W → ℕ) :
    (∑ p, weight (f p)) = ∑ c, ∑ v, count cell f c v * weight v := by
  classical
  have h := Finset.sum_fiberwise' Finset.univ (fun p ↦ (cell p, f p))
    (fun cv : C × W ↦ weight cv.2)
  simpa [count, Fintype.sum_prod_type] using h.symm

private theorem flattened_pair_count {P : Type} [Fintype P] {ell L : ℕ}
    (positions : Fin L ≃ P) (w : Fin 3 → P → CompleteWord ell) (i j : Fin 3) :
    (Finset.univ.filter (fun r ↦ (flatten positions rfl (w i) r).val = 1 ∧
      (flatten positions rfl (w j) r).val = 1)).card =
    ∑ p, (Finset.univ.filter (fun r ↦ (w i p r).val = 1 ∧ (w j p r).val = 1)).card := by
  classical
  let e : Fin (L * 2 ^ (ell - 1)) ≃ P × Fin (2 ^ (ell - 1)) :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr positions (Equiv.refl _))
  have h := e.sum_comp (fun pr ↦
    if (w i pr.1 pr.2).val = 1 ∧ (w j pr.1 pr.2).val = 1 then (1 : ℕ) else 0)
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  simpa only [Fintype.sum_prod_type] using h

/-- Integer joint profiles supply an intact-block extraction with directly computable dimensions. -/
theorem unbroken_matrix_extraction_of_joint_histogram
    {K : Type*} [Field K] {P C : Type} [Fintype P] [Fintype C] {ell L : ℕ}
    (positions : Fin L ≃ P) (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ)
    (joint : C → (Fin 3 → CompleteWord ell) → ℕ)
    (hmass : ∀ c, ∑ v, joint c v = Nat.card {p : P // cell p = c})
    (hmarginal : ∀ i c s, ∑ v, (if v i = s then joint c v else 0) = mu i c s)
    (hgrade : ∀ c v, 0 < joint c v → ∀ i, grade (v i) = shape c i)
    (hsupport : ∀ c v, 0 < joint c v →
      ∀ r, (v 0 r).val + (v 1 r).val + (v 2 r).val = 2) :
    let n := fun i j ↦ ∑ c, ∑ v, joint c v *
      (Finset.univ.filter (fun r ↦ (v i r).val = 1 ∧ (v j r).val = 1)).card
    Restrict (MMObj K (5 ^ n 0 2) (5 ^ n 0 1) (5 ^ n 1 2))
      (unbroken K 5 ell L positions cell shape mu) := by
  classical
  obtain ⟨w, hwgrade, hwmu, hwsupport, hwjoint⟩ :=
    supported_words_of_joint_histogram cell shape mu joint hmass hmarginal hgrade hsupport
  have h := mme_recursive_CW_unbroken_matrix_extraction_of_supported_words
    (K := K) positions cell shape mu w hwgrade hwmu hwsupport
  have hn (i j : Fin 3) :
      (Finset.univ.filter (fun r ↦ (flatten positions rfl (w i) r).val = 1 ∧
        (flatten positions rfl (w j) r).val = 1)).card =
      ∑ c, ∑ v, joint c v *
        (Finset.univ.filter (fun r ↦ (v i r).val = 1 ∧ (v j r).val = 1)).card := by
    rw [flattened_pair_count]
    have hs := histogram_weight_sum cell (fun p i ↦ w i p)
      (fun v ↦ (Finset.univ.filter (fun r ↦ (v i r).val = 1 ∧ (v j r).val = 1)).card)
    have hc (c v) : count cell (fun p i ↦ w i p) c v = joint c v := hwjoint c v
    simpa only [hc] using hs
  simpa only [hn] using h


theorem solution
    {K : Type*} [Field K] {P C : Type} [Fintype P] [Fintype C] {ell L : ℕ}
    (positions : Fin L ≃ P) (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ)
    (joint : C → (Fin 3 → CompleteWord ell) → ℕ)
    (hmass : ∀ c, ∑ v, joint c v = Nat.card {p : P // cell p = c})
    (hmarginal : ∀ i c s, ∑ v, (if v i = s then joint c v else 0) = mu i c s)
    (hgrade : ∀ c v, 0 < joint c v → ∀ i, grade (v i) = shape c i)
    (hsupport : ∀ c v, 0 < joint c v →
      ∀ r, (v 0 r).val + (v 1 r).val + (v 2 r).val = 2) :
    let n := fun i j ↦ ∑ c, ∑ v, joint c v *
      (Finset.univ.filter (fun r ↦ (v i r).val = 1 ∧ (v j r).val = 1)).card
    Restrict (MMObj K (5 ^ n 0 2) (5 ^ n 0 1) (5 ^ n 1 2))
      (unbroken K 5 ell L positions cell shape mu) := by
  exact unbroken_matrix_extraction_of_joint_histogram positions cell shape mu joint hmass hmarginal hgrade hsupport
#print axioms solution
