-- Prove2me | Theorems.Thm_mme_stothers_slice_entropy_minimum_exists_unique
-- name    : mme_stothers_slice_entropy_minimum_exists_unique
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-21T23:27:36.553325+00:00
-- url     : https://prove2.me/theorems/8154bcb6-891d-45b3-b270-b0d3999ea477
-- title:
--   Every marginal slice has a unique entropy minimizer
-- statement:
--   Let $Z=\{c\in\mathbb R_{\ge0}^{10}:\sum_i n_i c_i=1\}$ be the fourth-power profile simplex, with its positive class multiplicities $n_i$, and let $Y$ be the two-dimensional marginal kernel. Define $\mathcal E(c)=\prod_i c_i^{n_i c_i}$, taking the factor at a zero coordinate to be $1$.
--
--   For every $a\in Z$, there is exactly one $b\in Z$ such that $b-a\in Y$ and
--
--   $$\mathcal E(b)\le\mathcal E(c)\qquad\text{for every }c\in Z\text{ with }c-a\in Y.$$
--
--   This guarantees attainment and uniqueness of the entropy minimum used in the same-marginal correction. The statement includes boundary profiles; it does not assert that the minimizer has strictly positive coordinates.
-- source:
--   Derived existence-and-uniqueness refinement of the marginal-slice entropy minimization in A. M. Davie and A. J. Stothers, Improved bound for complexity of matrix multiplication, Proc. Roy. Soc. Edinburgh A 143 (2013), printed pp. 367-368, Equation (5.2) and proof of Lemma 5.2; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. This is not a separately numbered theorem in the source: it makes attainment explicit and strengthens convexity to uniqueness for the positive class multiplicities.

import Definitions.Def_mme_stothers_fourth_data
open MME.StothersFourth
set_option autoImplicit false

theorem mme_stothers_slice_entropy_minimum_exists_unique
    (a : Fin 10 → ℝ) (ha : InZ a) :
    ∃! b : Fin 10 → ℝ, InZ b ∧ InY (fun i ↦ b i - a i) ∧
      ∀ c : Fin 10 → ℝ, InZ c → InY (fun i ↦ c i - a i) →
        entropyProduct b ≤ entropyProduct c := by sorry
