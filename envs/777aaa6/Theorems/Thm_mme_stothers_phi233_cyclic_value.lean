-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_value
-- name    : mme_stothers_phi233_cyclic_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:21:08.776312+00:00
-- url     : https://prove2.me/theorems/9962a3a9-1247-4f5d-a8c5-ce6d86996605
-- title:
--   Davie--Stothers Lemma 5.1(v): the phi_233 value
-- statement:
--   For every field and every $\tau$ with $2\le 3\tau\le 3$, the cyclic symmetrization of the literal fourth-power constituent $\varphi_{233}$ has tau-value at least every fixed nonnegative base strictly below $$R_{233}=4(E+L)^2(2H+L)/L.$$ This leaf retains the nontrivial same-marginal fiber present in Davie--Stothers Lemma 5.1(v), rather than assuming uniqueness from the marginals.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v), printed p. 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 25.

import Definitions.Def_mme_stothers_fourth_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_value
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 9 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 2 3 3)) tau V := by
  sorry
