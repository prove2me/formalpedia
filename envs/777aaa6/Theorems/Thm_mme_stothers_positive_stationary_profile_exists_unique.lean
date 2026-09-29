-- Prove2me | Theorems.Thm_mme_stothers_positive_stationary_profile_exists_unique
-- name    : mme_stothers_positive_stationary_profile_exists_unique
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-21T23:32:31.626374+00:00
-- url     : https://prove2.me/theorems/ba9cf5c3-9d86-4f90-9321-927eba7a0f3e
-- title:
--   Every positive marginal slice has a unique positive stationary profile
-- statement:
--   Let $Z$ be the normalized nonnegative fourth-power profile simplex and let $Y$ be its marginal kernel. Let $\mathcal N\subseteq Z$ be the stationary set: in zero-based coordinates, its equations are $b_2b_7^2=b_4b_5b_9$ and $b_3b_7b_8=b_4b_6b_9$.
--
--   For every strictly positive $a\in Z$, there is exactly one strictly positive $b\in\mathcal N$ on the same marginal slice:
--
--   $$\exists!\,b\in\mathcal N:\quad (\forall i,\ b_i>0)\ \text{and}\ b-a\in Y.$$
--
--   This provides the stationary profile required by the same-marginal entropy correction from a positive admissible profile alone; its existence and uniqueness need not be supplied as additional hypotheses.
--
--   **Formalization Note** The stationary equations use the corrected fourth-power data interface.
-- source:
--   Derived existence-and-uniqueness characterization for A. M. Davie and A. J. Stothers, Improved bound for complexity of matrix multiplication, Proc. Roy. Soc. Edinburgh A 143 (2013), printed pp. 367-368, Equation (5.2), Lemma 5.2 and Theorem 5.3; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. This is not a separately numbered theorem in the source; it combines attained entropy minimization, the boundary-support argument, and the corrected stationarity equations.

import Definitions.Def_mme_stothers_fourth_data
open MME.StothersFourth
set_option autoImplicit false

theorem mme_stothers_positive_stationary_profile_exists_unique
    (a : Fin 10 → ℝ) (ha : InZ a) (hapos : ∀ i, 0 < a i) :
    ∃! b : Fin 10 → ℝ, InN b ∧ (∀ i, 0 < b i) ∧ InY (fun i ↦ b i - a i) := by sorry
