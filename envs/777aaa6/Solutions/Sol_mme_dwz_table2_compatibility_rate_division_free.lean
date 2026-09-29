-- Prove2me | solution 1 for mme_dwz_table2_compatibility_rate_division_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T12:33:59.088129+00:00
-- url     : https://prove2.me/submissions/3fba1166-4572-4018-ad90-6b40fcdf8c22

import Mathlib
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Theorems.Thm_mme_dwz_table2_integer_counts_exact
import Theorems.Thm_mme_dwz_table2_logAlphaP_integer_identity
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_typical_denominator_entropy_upper_of_factorization

open BigOperators Finset

set_option autoImplicit false
set_option warningAsError true

private theorem multinomial_entropy_polynomial_lower_all
    {R : Type*} [Fintype R] (w : R → ℕ)
    (m : ℕ) (hm : 0 < m) :
    Real.exp
        ((m : ℝ) * (((∑ i, w i : ℕ) : ℝ) * Real.log 2 *
          mme_modern_entropyBits
            (fun i ↦ (w i : ℝ) / ((∑ j, w j : ℕ) : ℝ)))) ≤
      (6 * (((∑ i, w i) * m + 1 : ℕ) : ℝ)) ^ Fintype.card R *
        (Nat.multinomial Finset.univ (fun i ↦ w i * m) : ℝ) := by
  by_cases hW : ∑ i, w i = 0
  · have hw : ∀ i, w i = 0 := by
      intro i
      exact Nat.eq_zero_of_le_zero
        (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ i) |>.trans_eq hW)
    simp [hw, Nat.multinomial]
    exact one_le_pow₀ (by norm_num)
  · exact mme_dwz_multinomial_entropy_polynomial_lower w m hm
      (Nat.pos_of_ne_zero hW)

/-!
The finite, division-free compatibility-rate estimate behind DWZ Lemma 6.7.
The exact factorization hypothesis is the typical-word denominator count.  No
division by that count occurs, so the statement remains meaningful when some
interior Table-2 masses are zero.
-/
theorem solution
    (m : ℕ) (hm : 0 < m) (B : ℕ)
    (hfactor :
      Nat.multinomial Finset.univ
          (fun p ↦ MME.DWZTable2Counts.gamma p * m) =
        Nat.multinomial Finset.univ
            (fun k ↦ MME.DWZTable2Counts.alphaZ k * m) * B) :
    (B : ℝ) * Real.exp
        ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
          MME.DWZSquare.logAlphaP) ≤
      (6 * ((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ)) ^ 5 *
      (∏ s : Fin 15,
        if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
          (6 * ((MME.DWZTable2Counts.component s * m + 1 : ℕ) : ℝ)) ^ 3
        else 1) *
      (∏ k : Fin 5,
        (6 * ((MME.DWZTable2Counts.plusMass k * m + 1 : ℕ) : ℝ)) ^ 3) *
      ((∏ s : Fin 15,
        if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
          (Nat.multinomial Finset.univ
            (fun r ↦ MME.DWZTable2Counts.split s r * m) : ℝ)
        else 1) *
      ∏ k : Fin 5,
        (Nat.multinomial Finset.univ
          (fun r ↦ MME.DWZTable2Counts.plusSplit k r * m) : ℝ)) := by
  let S : ℕ := MME.DWZTable2Counts.scale
  let Hg : ℝ := mme_modern_entropyBits
    (fun p ↦ (MME.DWZTable2Counts.gamma p : ℝ) / S)
  let Ha : ℝ := mme_modern_entropyBits
    (fun k ↦ (MME.DWZTable2Counts.alphaZ k : ℝ) / S)
  let Hb : ℝ := ∑ s : Fin 15,
    if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
      (MME.DWZTable2Counts.component s : ℝ) *
        mme_modern_entropyBits
          (fun r ↦ (MME.DWZTable2Counts.split s r : ℝ) /
            MME.DWZTable2Counts.component s)
    else 0
  let Hp : ℝ := ∑ k : Fin 5,
    (MME.DWZTable2Counts.plusMass k : ℝ) *
      mme_modern_entropyBits
        (fun r ↦ (MME.DWZTable2Counts.plusSplit k r : ℝ) /
          MME.DWZTable2Counts.plusMass k)
  let Eg : ℝ := (m : ℝ) * ((S : ℝ) * Real.log 2 * Hg)
  let Ea : ℝ := (m : ℝ) * ((S : ℝ) * Real.log 2 * Ha)
  let Eb : ℝ := (m : ℝ) * Real.log 2 * Hb
  let Ep : ℝ := (m : ℝ) * Real.log 2 * Hp
  let D : ℝ := (6 * ((S * m + 1 : ℕ) : ℝ)) ^ 5
  let Pb : ℝ := ∏ s : Fin 15,
    if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
      (6 * ((MME.DWZTable2Counts.component s * m + 1 : ℕ) : ℝ)) ^ 3
    else 1
  let Pi : ℝ := ∏ k : Fin 5,
    (6 * ((MME.DWZTable2Counts.plusMass k * m + 1 : ℕ) : ℝ)) ^ 3
  let Nb : ℝ := ∏ s : Fin 15,
    if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
      (Nat.multinomial Finset.univ
        (fun r ↦ MME.DWZTable2Counts.split s r * m) : ℝ)
    else 1
  let Ni : ℝ := ∏ k : Fin 5,
    (Nat.multinomial Finset.univ
      (fun r ↦ MME.DWZTable2Counts.plusSplit k r * m) : ℝ)
  rcases mme_dwz_table2_integer_counts_exact with
    ⟨_, _, hsplitSum, _, hgammaSum, halphaSum, hplusSum, _⟩
  have hSpos : 0 < S := by
    norm_num [S, MME.DWZTable2Counts.scale]
  have hden : (B : ℝ) ≤ D * Real.exp (Eg - Ea) := by
    have h := mme_dwz_typical_denominator_entropy_upper_of_factorization
      MME.DWZTable2Counts.gamma MME.DWZTable2Counts.alphaZ
      m hm (by simpa [S] using hgammaSum.trans halphaSum.symm)
      (by simpa [S, hgammaSum] using hSpos) B hfactor
    rw [hgammaSum, halphaSum] at h
    simpa only [D, Eg, Ea, Hg, Ha, S, Fintype.card_fin] using h
  have hboundaryLocal (s : Fin 15) :
      Real.exp
          ((m : ℝ) *
            ((MME.DWZTable2Counts.component s : ℝ) * Real.log 2 *
              mme_modern_entropyBits
              (fun r ↦ (MME.DWZTable2Counts.split s r : ℝ) /
                MME.DWZTable2Counts.component s))) ≤
        (6 * ((MME.DWZTable2Counts.component s * m + 1 : ℕ) : ℝ)) ^ 3 *
          (Nat.multinomial Finset.univ
            (fun r ↦ MME.DWZTable2Counts.split s r * m) : ℝ) := by
    have h := multinomial_entropy_polynomial_lower_all
      (MME.DWZTable2Counts.split s) m hm
    rw [hsplitSum s] at h
    simpa only [Fintype.card_fin] using h
  have hinteriorLocal (k : Fin 5) :
      Real.exp
          ((m : ℝ) *
            ((MME.DWZTable2Counts.plusMass k : ℝ) * Real.log 2 *
              mme_modern_entropyBits
              (fun r ↦ (MME.DWZTable2Counts.plusSplit k r : ℝ) /
                MME.DWZTable2Counts.plusMass k))) ≤
        (6 * ((MME.DWZTable2Counts.plusMass k * m + 1 : ℕ) : ℝ)) ^ 3 *
          (Nat.multinomial Finset.univ
            (fun r ↦ MME.DWZTable2Counts.plusSplit k r * m) : ℝ) := by
    have h := multinomial_entropy_polynomial_lower_all
      (MME.DWZTable2Counts.plusSplit k) m hm
    rw [hplusSum k] at h
    simpa only [Fintype.card_fin] using h
  have hEbSum : Eb = ∑ s : Fin 15,
      if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
        (m : ℝ) *
          ((MME.DWZTable2Counts.component s : ℝ) * Real.log 2 *
            mme_modern_entropyBits
            (fun r ↦ (MME.DWZTable2Counts.split s r : ℝ) /
              MME.DWZTable2Counts.component s))
      else 0 := by
    dsimp [Eb, Hb]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hboundary :
        MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0
    · simp only [hboundary, if_true]
      ring
    · simp only [hboundary, if_false, mul_zero]
  have hEpSum : Ep = ∑ k : Fin 5,
      (m : ℝ) *
        ((MME.DWZTable2Counts.plusMass k : ℝ) * Real.log 2 *
          mme_modern_entropyBits
          (fun r ↦ (MME.DWZTable2Counts.plusSplit k r : ℝ) /
            MME.DWZTable2Counts.plusMass k)) := by
    dsimp [Ep, Hp]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hboundary : Real.exp Eb ≤ Pb * Nb := by
    rw [hEbSum, Real.exp_sum]
    calc
      ∏ s : Fin 15,
          Real.exp
            (if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
              (m : ℝ) *
                ((MME.DWZTable2Counts.component s : ℝ) * Real.log 2 *
                  mme_modern_entropyBits
                  (fun r ↦ (MME.DWZTable2Counts.split s r : ℝ) /
                    MME.DWZTable2Counts.component s))
            else 0) ≤
          ∏ s : Fin 15,
            ((if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
                (6 * ((MME.DWZTable2Counts.component s * m + 1 : ℕ) : ℝ)) ^ 3
              else 1) *
            (if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
                (Nat.multinomial Finset.univ
                  (fun r ↦ MME.DWZTable2Counts.split s r * m) : ℝ)
              else 1)) := by
          apply Finset.prod_le_prod
          · intro s hs
            positivity
          · intro s hs
            by_cases hboundary :
                MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0
            · simpa [hboundary] using hboundaryLocal s
            · simp [hboundary]
      _ = Pb * Nb := by
        rw [Finset.prod_mul_distrib]
  have hinterior : Real.exp Ep ≤ Pi * Ni := by
    rw [hEpSum, Real.exp_sum]
    calc
      ∏ k : Fin 5,
          Real.exp
            ((m : ℝ) *
              ((MME.DWZTable2Counts.plusMass k : ℝ) * Real.log 2 *
                mme_modern_entropyBits
                (fun r ↦ (MME.DWZTable2Counts.plusSplit k r : ℝ) /
                  MME.DWZTable2Counts.plusMass k))) ≤
          ∏ k : Fin 5,
            ((6 * ((MME.DWZTable2Counts.plusMass k * m + 1 : ℕ) : ℝ)) ^ 3 *
              (Nat.multinomial Finset.univ
                (fun r ↦ MME.DWZTable2Counts.plusSplit k r * m) : ℝ)) := by
        apply Finset.prod_le_prod
        · intro k hk
          positivity
        · intro k hk
          exact hinteriorLocal k
      _ = Pi * Ni := by
        rw [Finset.prod_mul_distrib]
  have hnumerator : Real.exp (Eb + Ep) ≤ Pb * Pi * (Nb * Ni) := by
    rw [Real.exp_add]
    calc
      Real.exp Eb * Real.exp Ep ≤ (Pb * Nb) * (Pi * Ni) := by
        exact mul_le_mul hboundary hinterior (Real.exp_nonneg Ep) (by positivity)
      _ = Pb * Pi * (Nb * Ni) := by ring
  have hlog :
      (S : ℝ) * MME.DWZSquare.logAlphaP =
        (S : ℝ) * Ha - (S : ℝ) * Hg + Hb + Hp := by
    simpa [S, Ha, Hg, Hb, Hp] using
      mme_dwz_table2_logAlphaP_integer_identity
  have hrate :
      (m : ℝ) * (S : ℝ) * Real.log 2 * MME.DWZSquare.logAlphaP =
        Ea - Eg + Eb + Ep := by
    rw [show (m : ℝ) * (S : ℝ) * Real.log 2 * MME.DWZSquare.logAlphaP =
      (m : ℝ) * Real.log 2 *
        ((S : ℝ) * MME.DWZSquare.logAlphaP) by ring, hlog]
    dsimp [Ea, Eg, Eb, Ep]
    ring
  change (B : ℝ) * Real.exp
      ((m : ℝ) * (S : ℝ) * Real.log 2 * MME.DWZSquare.logAlphaP) ≤
    D * Pb * Pi * (Nb * Ni)
  rw [hrate]
  calc
    (B : ℝ) * Real.exp (Ea - Eg + Eb + Ep) ≤
        (D * Real.exp (Eg - Ea)) * Real.exp (Ea - Eg + Eb + Ep) := by
      exact mul_le_mul_of_nonneg_right hden (Real.exp_nonneg _)
    _ = D * Real.exp (Eb + Ep) := by
      rw [show D * Real.exp (Eg - Ea) * Real.exp (Ea - Eg + Eb + Ep) =
          D * (Real.exp (Eg - Ea) * Real.exp (Ea - Eg + Eb + Ep)) by ring]
      rw [← Real.exp_add]
      congr 2
      ring
    _ ≤ D * (Pb * Pi * (Nb * Ni)) := by
      exact mul_le_mul_of_nonneg_left hnumerator (by positivity)
    _ = D * Pb * Pi * (Nb * Ni) := by ring
