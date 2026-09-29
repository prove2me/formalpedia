-- Prove2me | Theorems.Thm_mme_dwz_table2_compatibility_rate_division_free
-- name    : mme_dwz_table2_compatibility_rate_division_free
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T12:33:47.699795+00:00
-- url     : https://prove2.me/theorems/e0da91fa-ef0d-4fa3-9fc8-a576d0eb41b2
-- title:
--   DWZ Lemma 6.7: finite Table 2 compatibility rate with polynomial loss
-- statement:
--   Fix a positive scaling multiplier m. Let B satisfy the exact typical-word factorization Mult(gamma*m) = Mult(alpha_Z*m) B for the integral Table 2 histograms at scale S = 10^16. Then B times exp(m S log(2) log_2(alpha_P)) is at most the product of: the five-cell denominator Stirling factor (6(Sm+1))^5; one three-cell Stirling factor for every boundary component; one three-cell Stirling factor for every interior (+,+,k) row; and the corresponding exact boundary and interior multinomial coefficients. The assertion is division-free and remains valid for the zero-mass interior rows. Equivalently, the exact numerator multinomial product divided conceptually by B has exponential rate at least alpha_P^(Sm), up to the displayed fixed-degree polynomial loss. This is the finite quantitative form of the compatibility calculation in Lemma 6.7 and Equation (23).
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Lemma 6.7 and Equation (23) (printed pp. 54-56 / PDF pp. 55-57), specialized to Section 6.3 Table 2.

import Mathlib
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Theorems.Thm_mme_dwz_table2_integer_counts_exact
import Theorems.Thm_mme_dwz_table2_logAlphaP_integer_identity
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_typical_denominator_entropy_upper_of_factorization

open BigOperators Finset

set_option autoImplicit false

theorem mme_dwz_table2_compatibility_rate_division_free
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
  sorry
