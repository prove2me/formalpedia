-- Prove2me | Theorems.Thm_mme_stothers_corrected_global_rate_feasible_bounds
-- name    : mme_stothers_corrected_global_rate_feasible_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T15:20:51.381369+00:00
-- url     : https://prove2.me/theorems/24fc8502-f5dd-4555-b132-01b6dbf8f681
-- title:
--   Positivity and comparison of the corrected Stothers rate
-- statement:
--   Let $q$ be a positive integer, $\tau$ any real number, and $a,b$ strictly positive ten-tuples satisfying the Stothers feasibility conditions $a\in Z$, $b\in\mathcal N$, and $a-b\in Y=\ker Q$. Then
--
--   $$0<R_{\mathrm{corr}}(q,\tau,a,b)\le R_{\mathrm{old}}(q,\tau,a,b).$$
--
--   Here $a$ remains the retained profile in the constituent-value powers. The corrected rate contains the target-to-ambient loss $P(b)/P(a)$, while the old rate contains its reciprocal, with $P(x)=\prod_i x_i^{n_i x_i}$. This comparison establishes the direction of the correction under the exact feasible-profile hypotheses. It is an algebraic comparison of rates, not a tensor-value theorem, and requires no interval restriction on $\tau$.
-- source:
--   Davie and Stothers (2013), Equation (3.4), printed pp. 358–359, Lemma 5.2 and Equation (5.3), printed p. 368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; Stothers (2010), Chapter 4.2, printed pp. 78–81, https://era.ed.ac.uk/handle/1842/4734. The new rate takes P(b)/P(a) from the target/ambient counting derivation and thesis, correcting the reciprocal orientation printed in Eq. (5.3).

import Definitions.Def_mme_stothers_corrected_global_rate

open MME BigOperators MME.StothersFourth

set_option autoImplicit false

theorem mme_stothers_corrected_global_rate_feasible_bounds
    (q : ℕ) (hq : 0 < q) (tau : ℝ) (a b : Fin 10 → ℝ)
    (ha : InZ a) (hb : InN b)
    (haPos : ∀ i : Fin 10, 0 < a i)
    (hbPos : ∀ i : Fin 10, 0 < b i)
    (hsame : InY (fun i ↦ a i - b i)) :
    0 < correctedGlobalRate q tau a b ∧
      correctedGlobalRate q tau a b ≤ globalRate q tau a b := by
  sorry
