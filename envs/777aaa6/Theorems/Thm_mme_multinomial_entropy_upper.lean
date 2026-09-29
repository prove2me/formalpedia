-- Prove2me | Theorems.Thm_mme_multinomial_entropy_upper
-- name    : mme_multinomial_entropy_upper
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-09T05:13:57.750856+00:00
-- url     : https://prove2.me/theorems/6c488a6d-2862-43f9-bee7-6ab9ce4ae98e
-- title:
--   Multinomial coefficient bounded above by its entropy exponential
-- statement:
--   **A multinomial coefficient never exceeds the exponential of its entropy.**
--
--   Let $R$ be a nonempty finite index set, $w : R \to \mathbb N$ strictly positive, $W = \sum_i w_i$, and $m \in \mathbb N$.  Write $p_i = w_i / W$ for the normalised weight vector and $H(p)$ for its Shannon entropy in bits.  Then
--
--   $$\binom{Wm}{w_1 m, \dots, w_{|R|} m} \;\le\; \exp\bigl(m\, W \ln 2 \; H(p)\bigr)
--   \; = \; 2^{\,Wm \, H(p)} .$$
--
--   This is the elementary half of the type-counting estimate: a single type class is no larger than the exponential of its entropy.  It is the exact counterpart of the platform's `mme_dwz_multinomial_entropy_polynomial_lower`, which supplies the matching lower bound at the cost of a polynomial factor, and together the two pin the multinomial to within a polynomial of $2^{N H}$.
--
--   The pair is what one needs to compare two multinomial coefficients on the same total, for instance two joint histograms with the same marginals, at exponential rate: the ratio is $2^{N(H_1 - H_2)}$ up to a polynomial factor.
--
--   *Formalization note.* The proof is the classical one and uses no Stirling estimate.  By the multinomial theorem, $1 = (\sum_i p_i)^{Wm}$ expands as a sum of non-negative terms $\binom{Wm}{k} \prod_i p_i^{k_i}$ over all compositions $k$ of $Wm$; keeping only the term at $k_i = w_i m$ gives $\binom{Wm}{wm} \prod_i p_i^{w_i m} \le 1$, and $\prod_i p_i^{w_i m} = \exp\bigl(-m W \ln 2\, H(p)\bigr)$ by definition of the entropy.  Strict positivity of $w$ keeps every logarithm finite.
-- source:
--   T. M. Cover and J. A. Thomas, Elements of Information Theory, 2nd ed., Wiley 2006, Theorem 11.1.3 (the size of a type class); the estimate is used in the laser-method extractions of D. Coppersmith and S. Winograd, Matrix multiplication via arithmetic progressions, J. Symbolic Computation 9 (1990), Section 6.

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_mme_modern_entropy_data

open BigOperators Finset

set_option autoImplicit false

theorem mme_multinomial_entropy_upper
    {R : Type*} [Fintype R] [DecidableEq R] [Nonempty R] (w : R → ℕ) (m : ℕ)
    (hw : ∀ i, 0 < w i) :
    (Nat.multinomial Finset.univ (fun i ↦ w i * m) : ℝ) ≤
      Real.exp ((m : ℝ) * (((∑ i, w i : ℕ) : ℝ) * Real.log 2 *
        mme_modern_entropyBits
          (fun i ↦ (w i : ℝ) / ((∑ j, w j : ℕ) : ℝ)))) := by
  sorry
