-- Prove2me | Theorems.Thm_mme_stothers_phi125_cyclic_value
-- name    : mme_stothers_phi125_cyclic_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:20:56.511915+00:00
-- url     : https://prove2.me/theorems/17b07a58-adb2-48c4-9d9d-ca1707c2df4c
-- title:
--   Davie--Stothers Lemma 5.1(ii): the phi_125 value
-- statement:
--   For every field and every $\tau$ with $2\le 3\tau\le 3$, the cyclic symmetrization of the literal fourth-power constituent $\varphi_{125}$ has tau-value at least every fixed nonnegative base strictly below $$R_{125}=4(L+EH)(2H+L)/H.$$ The strict-lower formulation retains the subexponential losses in the source's finite extraction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(ii), printed pp. 364-365, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 22.

import Definitions.Def_mme_stothers_fourth_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi125_cyclic_value
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 6 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)) tau V := by
  sorry
