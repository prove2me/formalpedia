-- Prove2me | Theorems.Thm_mme_stothers_lemma51_remaining_four_values
-- name    : mme_stothers_lemma51_remaining_four_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:36:57.394927+00:00
-- url     : https://prove2.me/theorems/b1695ae4-fd09-4fbf-8600-0b20d0e41ed2
-- title:
--   Davie--Stothers Lemma 5.1(ii)--(v): the remaining four recursive values
-- statement:
--   For every field and every $\tau$ with $2\le3\tau\le3$, the cyclic symmetrizations of the four literal fourth-power constituents
--
--   $$
--   \varphi_{125},\qquad\varphi_{134},\qquad\varphi_{224},\qquad\varphi_{233}
--   $$
--
--   have tau-value at least every fixed nonnegative base strictly below, respectively, the four rates $R_{125},R_{134},R_{224},R_{233}$ displayed in Davie--Stothers Lemma 5.1(ii)--(v).
--
--   This bundle is the remaining source-level recursive constituent package after separating the completed algebraic structure and outer extraction of $\varphi_{116}$. Each clause uses the literal constituent and the strict-lower-base formulation required to absorb subexponential pruning losses.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(ii)--(v), printed pp. 364-366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemmas 22--25, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf.

import Definitions.Def_mme_stothers_fourth_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_lemma51_remaining_four_values
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    (∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 6 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)) tau V) ∧
    (∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 7 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)) tau V) ∧
    (∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 8 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 2 2 4)) tau V) ∧
    (∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 9 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 2 3 3)) tau V) := by
  sorry
