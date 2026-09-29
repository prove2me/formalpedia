-- Prove2me | Theorems.Thm_mme_stothers_slice_entropy_minimum_support
-- name    : mme_stothers_slice_entropy_minimum_support
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-21T23:30:56.767077+00:00
-- url     : https://prove2.me/theorems/e332c203-942a-4b62-a3ea-7c3a260d83da
-- title:
--   Entropy minimizers retain every feasible positive coordinate
-- statement:
--   Let $Z$ be the normalized nonnegative fourth-power profile simplex, with positive class multiplicities $n_i$, and let $Y$ be its marginal kernel. Write $\mathcal E(c)=\prod_i c_i^{n_i c_i}$, interpreting each factor at a zero coordinate as $1$.
--
--   Suppose $a,b\in Z$, $b-a\in Y$, and $b$ minimizes $\mathcal E$ over all $c\in Z$ with $c-a\in Y$. Then
--
--   $$a_k>0\quad\Longrightarrow\quad b_k>0\qquad\text{for every coordinate }k.$$
--
--   In particular, if a marginal slice contains a strictly positive profile, its entropy minimizer is strictly positive. This supplies the interiority needed to identify the attained minimum with a stationary profile.
-- source:
--   Derived boundary-support lemma for the entropy minimization in A. M. Davie and A. J. Stothers, Improved bound for complexity of matrix multiplication, Proc. Roy. Soc. Edinburgh A 143 (2013), printed pp. 367-368, Equation (5.2) and proof of Lemma 5.2; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. This is an explicit supporting lemma, not a separately numbered theorem in the source.

import Definitions.Def_mme_stothers_fourth_data
open MME.StothersFourth
set_option autoImplicit false

theorem mme_stothers_slice_entropy_minimum_support
    (a b : Fin 10 → ℝ) (ha : InZ a) (hb : InZ b)
    (hba : InY (fun i ↦ b i - a i))
    (hmin : ∀ c : Fin 10 → ℝ, InZ c → InY (fun i ↦ c i - a i) →
      entropyProduct b ≤ entropyProduct c) :
    ∀ k, 0 < a k → 0 < b k := by sorry
