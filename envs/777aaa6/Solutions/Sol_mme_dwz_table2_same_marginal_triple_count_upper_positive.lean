-- Prove2me | solution 1 for mme_dwz_table2_same_marginal_triple_count_upper_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:21:21.483412+00:00
-- url     : https://prove2.me/submissions/63c76122-d162-478f-8d84-3ebd18809e55

import Theorems.Thm_mme_finite_word_family_histogram_entropy_upper
import Theorems.Thm_mme_dwz_table2_empirical_histogram_entropy_le_max

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 250000

theorem solution (m : ℕ) (hm : 0 < m) :
    let sourceLength := MME.DWZTable2Counts.scale * m
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    let MarginalTriple :=
      {w : Fin sourceLength → Fin 15 //
        (∀ x, Fintype.card
            {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
        (∀ y, Fintype.card
            {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
        ∀ z, Fintype.card
            {t // MME.DWZSquare.shapeZ (w t) = z} =
              MME.DWZTable2Counts.alphaZ z * m}
    (Nat.card MarginalTriple : ℝ) ≤
      (((sourceLength + 1 : ℕ) : ℝ)) ^ 15 *
        Real.exp
          ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
            MME.DWZSquare.maxSameMarginalEntropy) := by
  classical
  dsimp only
  let sourceLength := MME.DWZTable2Counts.scale * m
  let alphaX : Fin 5 → ℕ := fun x ↦
    ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
      MME.DWZTable2Counts.component s.1 * m
  let alphaY : Fin 5 → ℕ := fun y ↦
    ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
      MME.DWZTable2Counts.component s.1 * m
  let MarginalTriple :=
    {w : Fin sourceLength → Fin 15 //
      (∀ x, Fintype.card
          {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
      (∀ y, Fintype.card
          {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
      ∀ z, Fintype.card
          {t // MME.DWZSquare.shapeZ (w t) = z} =
            MME.DWZTable2Counts.alphaZ z * m}
  have hsourcePos : 0 < sourceLength := by
    dsimp only [sourceLength]
    exact Nat.mul_pos (by norm_num [MME.DWZTable2Counts.scale]) hm
  let F : Finset (Fin sourceLength → Fin 15) :=
    Finset.univ.image (fun w : MarginalTriple ↦ w.1)
  have hFCard : F.card = Nat.card MarginalTriple := by
    dsimp only [F]
    rw [Finset.card_image_of_injective Finset.univ Subtype.val_injective,
      Finset.card_univ, ← Nat.card_eq_fintype_card]
  have hEntropy (f : Fin sourceLength → Fin 15) (hf : f ∈ F) :
      mme_modern_entropyBits
          (fun s ↦
            (Fintype.card {t : Fin sourceLength // f t = s} : ℝ) /
              (sourceLength : ℝ)) ≤
        MME.DWZSquare.maxSameMarginalEntropy := by
    rcases Finset.mem_image.mp hf with ⟨w, hw, rfl⟩
    exact (mme_dwz_table2_empirical_histogram_entropy_le_max m hm w).2
  have h := mme_finite_word_family_histogram_entropy_upper
    sourceLength hsourcePos F MME.DWZSquare.maxSameMarginalEntropy hEntropy
  rw [hFCard] at h
  have hExp :
      (sourceLength : ℝ) * Real.log 2 *
          MME.DWZSquare.maxSameMarginalEntropy =
        (m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
          MME.DWZSquare.maxSameMarginalEntropy := by
    dsimp only [sourceLength]
    push_cast
    ring
  rw [hExp] at h
  simpa only [Fintype.card_fin] using h
