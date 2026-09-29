-- Prove2me | Theorems.Thm_mme_stothers_positive_stationary_profile_unique
-- name    : mme_stothers_positive_stationary_profile_unique
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-21T23:23:14.07915+00:00
-- url     : https://prove2.me/theorems/dbcbe5c1-c671-49cf-8247-648963b67318
-- title:
--   Uniqueness of a positive stationary profile on a marginal slice
-- statement:
--   Let $Z$ be the normalized nonnegative fourth-power profile space, let $Y$ be its marginal kernel, and let $\mathcal N\subseteq Z$ be the stationary set. In zero-based coordinates its defining equations are $c_2c_7^2=c_4c_5c_9$ and $c_3c_7c_8=c_4c_6c_9$.
--
--   If $a,b\in\mathcal N$ have strictly positive coordinates and $a-b\in Y$, then
--
--   $$a=b.$$
--
--   Thus each marginal slice has at most one positive stationary profile. Together with the necessity of stationarity at a positive entropy minimum, this gives uniqueness of positive minimizers of $\prod_i c_i^{n_i c_i}$ on that slice.
--
--   **Formalization Note** The equations follow the corrected fourth-power data interface, with coordinates indexed from zero.
-- source:
--   Derived uniqueness refinement of the entropy argument in A. M. Davie and A. J. Stothers, Improved bound for complexity of matrix multiplication, Proc. Roy. Soc. Edinburgh A 143 (2013), printed pp. 367-368, Equation (5.2) and proof of Lemma 5.2; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. This is not a separately numbered source theorem. Stationarity equations use the corrected platform interface, as documented in its Lemma 5.2 entry.

import Definitions.Def_mme_stothers_fourth_data
open MME.StothersFourth
set_option autoImplicit false

theorem mme_stothers_positive_stationary_profile_unique
    (a b : Fin 10 → ℝ) (ha : InN a) (hb : InN b)
    (hapos : ∀ i, 0 < a i) (hbpos : ∀ i, 0 < b i)
    (hsame : InY (fun i ↦ a i - b i)) : a = b := by sorry
