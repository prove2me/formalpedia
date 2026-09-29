-- Prove2me | Theorems.Thm_mme_stothers_corrected_global_rate_algebra
-- name    : mme_stothers_corrected_global_rate_algebra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T15:17:07.585039+00:00
-- url     : https://prove2.me/theorems/93be89e4-6e54-4c3b-a921-6f9dd9899f09
-- title:
--   Factorization and diagonal agreement of the corrected Stothers rate
-- statement:
--   Let $q$ be a natural number, $\tau$ a real number, and $a,b$ nonnegative real ten-tuples. Write $n_i$ for the Table-1 multiplicities and set
--
--   $$
--   P(x)=\prod_i x_i^{n_i x_i},\qquad C=\prod_i\left(v_i(q,\tau)^{a_i/3}\right)^{n_i},\qquad M=\prod_j (Qa/3)_j^{-(Qa/3)_j}.
--   $$
--
--   Then the corrected and previously published rates satisfy
--
--   $$
--   R_{\mathrm{corr}}(q,\tau,a,b)=C\frac{P(b)}{P(a)}M,\qquad R_{\mathrm{old}}(q,\tau,a,b)=C\frac{P(a)}{P(b)}M.
--   $$
--
--   On every diagonal profile they agree:
--
--   $$R_{\mathrm{corr}}(q,\tau,a,a)=R_{\mathrm{old}}(q,\tau,a,a).$$
--
--   These identities isolate the changed entropy factor while preserving the retained-profile constituent powers. In particular they identify the corrected rate with the one used in the completed equal-profile Stothers endpoint. No tensor extraction is asserted. Zero coordinates use Lean's total real-power and division conventions.
-- source:
--   Davie and Stothers (2013), Improved Bound for Complexity of Matrix Multiplication, Equation (3.4), printed pp. 358–359, and comparison with Equation (5.3), printed p. 368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; Stothers (2010), On the Complexity of Matrix Multiplication, Chapter 4.2, printed pp. 78–81, https://era.ed.ac.uk/handle/1842/4734. The separately named rate uses the target/ambient entropy-loss orientation P(b)/P(a) from the derivation, correcting the reciprocal orientation printed in Eq. (5.3).

import Definitions.Def_mme_stothers_corrected_global_rate

open MME BigOperators MME.StothersFourth

set_option autoImplicit false

theorem mme_stothers_corrected_global_rate_algebra
    (q : ℕ) (tau : ℝ) (a b : Fin 10 → ℝ)
    (ha : ∀ i : Fin 10, 0 ≤ a i)
    (hb : ∀ i : Fin 10, 0 ≤ b i) :
    correctedGlobalRate q tau a b =
        (∏ i, (Real.rpow (classValue q tau i) (a i / 3)) ^
          classMultiplicity i) *
        (entropyProduct b / entropyProduct a) *
        (∏ j, Real.rpow (marginal a j) (-marginal a j)) ∧
      globalRate q tau a b =
        (∏ i, (Real.rpow (classValue q tau i) (a i / 3)) ^
          classMultiplicity i) *
        (entropyProduct a / entropyProduct b) *
        (∏ j, Real.rpow (marginal a j) (-marginal a j)) ∧
      correctedGlobalRate q tau a a = globalRate q tau a a := by
  sorry
