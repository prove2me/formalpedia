-- Prove2me | solution 1 for mme_dwz_table2_logAlphaP_integer_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T12:17:52.05691+00:00
-- url     : https://prove2.me/submissions/619cbd9a-0764-492f-a350-19ac4a68d807

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open BigOperators Finset

set_option autoImplicit false

private theorem normalized_of_scaled
    {I : Type*} [Fintype I]
    (S : ℕ) (hS : 0 < S) (p : I → ℝ) (w : I → ℕ)
    (hscaled : ∀ i, (S : ℝ) * p i = w i) :
    (fun i ↦ (w i : ℝ) / (S : ℝ)) = p := by
  have hSR : (S : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hS)
  funext i
  rw [← hscaled i]
  field_simp

private theorem conditional_normalized_of_scaled
    {I : Type*} [Fintype I]
    (S : ℕ) (hS : 0 < S) (a : ℝ) (c : ℕ)
    (q : I → ℝ) (w : I → ℕ)
    (ha : a ≠ 0)
    (hcount : (S : ℝ) * a = c)
    (hscaled : ∀ i, (S : ℝ) * a * q i = w i) :
    (fun i ↦ (w i : ℝ) / (c : ℝ)) = q := by
  have hSR : (S : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hS)
  funext i
  rw [← hscaled i, ← hcount]
  field_simp

theorem solution :
    (MME.DWZTable2Counts.scale : ℝ) * MME.DWZSquare.logAlphaP =
      (MME.DWZTable2Counts.scale : ℝ) *
          mme_modern_entropyBits
            (fun k ↦ (MME.DWZTable2Counts.alphaZ k : ℝ) /
              MME.DWZTable2Counts.scale) -
      (MME.DWZTable2Counts.scale : ℝ) *
          mme_modern_entropyBits
            (fun p ↦ (MME.DWZTable2Counts.gamma p : ℝ) /
              MME.DWZTable2Counts.scale) +
      (∑ s : Fin 15,
        if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
          (MME.DWZTable2Counts.component s : ℝ) *
            mme_modern_entropyBits
              (fun r ↦ (MME.DWZTable2Counts.split s r : ℝ) /
                MME.DWZTable2Counts.component s)
        else 0) +
      ∑ k : Fin 5,
        (MME.DWZTable2Counts.plusMass k : ℝ) *
          mme_modern_entropyBits
            (fun r ↦ (MME.DWZTable2Counts.plusSplit k r : ℝ) /
              MME.DWZTable2Counts.plusMass k) := by
  let S := MME.DWZTable2Counts.scale
  have hS : 0 < S := by norm_num [S, MME.DWZTable2Counts.scale]
  obtain ⟨hcomponentExact, hsplitExact, _, _, _, _, _, hgammaExact,
      halphaZExact, hplusMassExact, hplusSplitExact⟩ :=
    mme_dwz_table2_integer_counts_exact
  have hgamma :
      (fun p ↦ (MME.DWZTable2Counts.gamma p : ℝ) / (S : ℝ)) =
        MME.DWZSquare.gamma := by
    exact normalized_of_scaled S hS _ _ hgammaExact
  have halphaZ :
      (fun k ↦ (MME.DWZTable2Counts.alphaZ k : ℝ) / (S : ℝ)) =
        mme_modern_marginal MME.DWZSquare.shapeZ MME.DWZSquare.alpha := by
    exact normalized_of_scaled S hS _ _ halphaZExact
  have hsplit (s : Fin 15) :
      (fun r ↦ (MME.DWZTable2Counts.split s r : ℝ) /
        (MME.DWZTable2Counts.component s : ℝ)) =
        MME.DWZSquare.zSplit s := by
    exact conditional_normalized_of_scaled S hS
      (MME.DWZSquare.alpha s) (MME.DWZTable2Counts.component s)
      (MME.DWZSquare.zSplit s) (MME.DWZTable2Counts.split s)
      (ne_of_gt (MME.DWZSquare.alpha_pos s))
      (hcomponentExact s) (hsplitExact s)
  have hboundary :
      (∑ s : Fin 15,
        if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
          (MME.DWZTable2Counts.component s : ℝ) *
            mme_modern_entropyBits
              (fun r ↦ (MME.DWZTable2Counts.split s r : ℝ) /
                MME.DWZTable2Counts.component s)
        else 0) =
      (S : ℝ) *
        (∑ s : Fin 15,
          if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
            MME.DWZSquare.alpha s *
              mme_modern_entropyBits (MME.DWZSquare.zSplit s)
          else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : MME.DWZSquare.shapeX s = 0 ∨
        MME.DWZSquare.shapeY s = 0
    · simp only [hs, if_true]
      rw [hsplit s, ← hcomponentExact s]
      ring
    · simp [hs]
  have hinteriorTerm (k : Fin 5) :
      (MME.DWZTable2Counts.plusMass k : ℝ) *
          mme_modern_entropyBits
            (fun r ↦ (MME.DWZTable2Counts.plusSplit k r : ℝ) /
              MME.DWZTable2Counts.plusMass k) =
        (S : ℝ) * (MME.DWZSquare.plusMass k *
          mme_modern_entropyBits (MME.DWZSquare.plusSplit k)) := by
    by_cases hk : MME.DWZSquare.plusMass k = 0
    · have hcountZero : (MME.DWZTable2Counts.plusMass k : ℝ) = 0 := by
        rw [← hplusMassExact k, hk]
        ring
      simp [hk, hcountZero]
    · have hnormalized :
          (fun r ↦ (MME.DWZTable2Counts.plusSplit k r : ℝ) /
            (MME.DWZTable2Counts.plusMass k : ℝ)) =
            MME.DWZSquare.plusSplit k := by
        exact conditional_normalized_of_scaled S hS
          (MME.DWZSquare.plusMass k)
          (MME.DWZTable2Counts.plusMass k)
          (MME.DWZSquare.plusSplit k)
          (MME.DWZTable2Counts.plusSplit k) hk
          (hplusMassExact k) (hplusSplitExact k)
      rw [hnormalized, ← hplusMassExact k]
      ring
  have hinterior :
      (∑ k : Fin 5,
        (MME.DWZTable2Counts.plusMass k : ℝ) *
          mme_modern_entropyBits
            (fun r ↦ (MME.DWZTable2Counts.plusSplit k r : ℝ) /
              MME.DWZTable2Counts.plusMass k)) =
      (S : ℝ) *
        (∑ k : Fin 5, MME.DWZSquare.plusMass k *
          mme_modern_entropyBits (MME.DWZSquare.plusSplit k)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ ↦ hinteriorTerm k)
  change (S : ℝ) * MME.DWZSquare.logAlphaP = _
  rw [hgamma, halphaZ, hboundary, hinterior]
  unfold MME.DWZSquare.logAlphaP
  ring
