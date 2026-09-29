-- Prove2me | Theorems.Thm_mme_stothers_phi134_cyclic_value
-- name    : mme_stothers_phi134_cyclic_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:20:49.490465+00:00
-- url     : https://prove2.me/theorems/6a506861-84e1-439a-9f11-12a9641c5df4
-- title:
--   Davie--Stothers Lemma 5.1(iii): the phi_134 value
-- statement:
--   For every field and every $\tau$ with $2\le 3\tau\le 3$, the cyclic symmetrization of the literal fourth-power constituent $\varphi_{134}$ has tau-value at least every fixed nonnegative base strictly below $$R_{134}=4(E+L)(2+2E+H).$$ The theorem isolates the third constituent analysis in Davie--Stothers Lemma 5.1.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(iii), printed p. 365, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 23.

import Definitions.Def_mme_stothers_fourth_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi134_cyclic_value
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 7 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)) tau V := by
  sorry
