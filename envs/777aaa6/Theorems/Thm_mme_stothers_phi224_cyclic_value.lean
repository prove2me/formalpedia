-- Prove2me | Theorems.Thm_mme_stothers_phi224_cyclic_value
-- name    : mme_stothers_phi224_cyclic_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:21:02.975143+00:00
-- url     : https://prove2.me/theorems/f4cbe891-8c47-4f66-967f-f3157fc0d5b0
-- title:
--   Davie--Stothers Lemma 5.1(iv): the phi_224 value
-- statement:
--   For every field and every $\tau$ with $2\le 3\tau\le 3$, the cyclic symmetrization of the literal fourth-power constituent $\varphi_{224}$ has tau-value at least every fixed nonnegative base strictly below $$R_{224}=(2H+L)^2(2+2E+H)/H.$$ This is the fourth constituent analysis in Davie--Stothers Lemma 5.1.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(iv), printed pp. 365-366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 24.

import Definitions.Def_mme_stothers_fourth_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi224_cyclic_value
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 8 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 2 2 4)) tau V := by
  sorry
