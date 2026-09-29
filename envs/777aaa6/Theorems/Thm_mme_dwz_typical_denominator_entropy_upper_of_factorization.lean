-- Prove2me | Theorems.Thm_mme_dwz_typical_denominator_entropy_upper_of_factorization
-- name    : mme_dwz_typical_denominator_entropy_upper_of_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T11:54:21.039771+00:00
-- url     : https://prove2.me/theorems/5968054d-c0a8-4e6c-8c95-caa4d10b9e4d
-- title:
--   DWZ Lemma 6.7: division-free entropy bound for the typical-block denominator
-- statement:
--   Let `gamma` and `alphaZ` be finite nonnegative integer histograms of the same positive total mass, and scale both by a positive integer $m$. Suppose an exact fiber count $B$ satisfies
--
--   $$
--   \operatorname{Mult}(m\gamma)=\operatorname{Mult}(m\alpha_Z)\,B.
--   $$
--
--   Then, without dividing natural cardinalities,
--
--   $$
--   B\le \bigl(6(Wm+1)\bigr)^{|\mathrm{Coarse}|}
--   \exp(E_\gamma-E_{\alpha_Z}),
--   $$
--
--   where $W=\sum\gamma=\sum\alpha_Z$ and $E_w=mW\log(2)H_2(w/W)$. Applied to the exact factorization in `mme_dwz_lemma6_7_typical_denominator_count`, this is the upper entropy estimate for $|B_{\mathrm{typical},K}|$ in the denominator following DWZ Equation (23). The fixed-degree polynomial is the only loss.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Section 6.2, Lemma 6.7 denominator calculation immediately after Equation (23), printed pp. 55-56 (PDF pp. 56-57).

import Mathlib
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_multinomial_entropy_upper

open scoped BigOperators
set_option autoImplicit false

theorem mme_dwz_typical_denominator_entropy_upper_of_factorization
    {Fine Coarse : Type*} [Fintype Fine] [Fintype Coarse]
    (gamma : Fine → ℕ) (alphaZ : Coarse → ℕ)
    (m : ℕ) (hm : 0 < m)
    (hsum : ∑ i, gamma i = ∑ k, alphaZ k)
    (hW : 0 < ∑ i, gamma i)
    (B : ℕ)
    (hfactor :
      Nat.multinomial Finset.univ (fun i ↦ gamma i * m) =
        Nat.multinomial Finset.univ (fun k ↦ alphaZ k * m) * B) :
    (B : ℝ) ≤
      (6 * (((∑ k, alphaZ k) * m + 1 : ℕ) : ℝ)) ^ Fintype.card Coarse *
        Real.exp (
          (m : ℝ) * (((∑ i, gamma i : ℕ) : ℝ) * Real.log 2 *
            mme_modern_entropyBits
              (fun i ↦ (gamma i : ℝ) / ((∑ j, gamma j : ℕ) : ℝ))) -
          (m : ℝ) * (((∑ k, alphaZ k : ℕ) : ℝ) * Real.log 2 *
            mme_modern_entropyBits
              (fun k ↦ (alphaZ k : ℝ) / ((∑ l, alphaZ l : ℕ) : ℝ)))) := by sorry
