-- Prove2me | Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
-- name    : mme_dwz_multinomial_entropy_polynomial_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T11:24:11.708351+00:00
-- url     : https://prove2.me/theorems/2e42e907-1a53-420b-910e-0dae2ae915a9
-- title:
--   Integral multinomial types retain their Shannon rate up to polynomial loss
-- statement:
--   Let `w` be a nonzero finite vector of nonnegative integer weights, let $W=\sum_i w_i$, and scale it by any positive integer $m$.  For the rational distribution $p_i=w_i/W$, the corresponding multinomial coefficient satisfies
--
--   $$
--   \exp\bigl(mW\log(2)H_2(p)\bigr)
--   \le \bigl(6(Wm+1)\bigr)^{|R|}
--   \binom{Wm}{(w_i m)_{i\in R}}.
--   $$
--
--   Thus the exact integral type class retains the full Shannon-entropy exponential rate with only an explicit fixed-degree polynomial loss. Zero-weight symbols are allowed. This is the reusable Stirling step needed after the exact disjoint-region count in DWZ Equation (23): every rational restricted-split distribution is represented by an integer numerator vector `w`, and the cofinal scales are its positive multiples `m`.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Section 6.2, Lemma 6.7 and Equation (23), printed pp. 54-56 (PDF pp. 55-57); the factorial bounds are formalized from Mathlib's Stirling theorem.

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_modern_entropy_data

open scoped BigOperators
open Filter
set_option autoImplicit false

theorem mme_dwz_multinomial_entropy_polynomial_lower
    {R : Type*} [Fintype R] (w : R → ℕ)
    (m : ℕ) (hm : 0 < m) (hW : 0 < ∑ i, w i) :
    Real.exp
        ((m : ℝ) * (((∑ i, w i : ℕ) : ℝ) * Real.log 2 *
          mme_modern_entropyBits
            (fun i ↦ (w i : ℝ) / ((∑ j, w j : ℕ) : ℝ)))) ≤
      (6 * (((∑ i, w i) * m + 1 : ℕ) : ℝ)) ^ Fintype.card R *
        (Nat.multinomial Finset.univ (fun i ↦ w i * m) : ℝ) := by sorry
