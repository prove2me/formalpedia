-- Prove2me | Theorems.Thm_mme_stothers_lemma51_recursive_values
-- name    : mme_stothers_lemma51_recursive_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-29T00:20:08.545504+00:00
-- url     : https://prove2.me/theorems/391e8551-6ca0-4a60-a0ad-fe6b826f1506
-- title:
--   Lemma 5.1: five recursive fourth-power constituent values
-- statement:
--   Let $K$ be an arbitrary field and let $\tau\in\mathbb R$ satisfy $2\le3\tau\le3$. Put
--
--   $$
--   E=(12)^{3\tau},\qquad H=(38)^{3\tau},\qquad
--   L=4\,6^{3\tau}(6^{3\tau}+2).
--   $$
--
--   Write
--
--   $$
--   \begin{aligned}
--   R_{116}&=4(E^2+2L),\\
--   R_{125}&=4(L+EH)(2H+L)/H,\\
--   R_{134}&=4(E+L)(2+2E+H),\\
--   R_{224}&=(2H+L)^2(2+2E+H)/H,\\
--   R_{233}&=4(E+L)^2(2H+L)/L.
--   \end{aligned}
--   $$
--
--   For each row and every fixed real $V$ with $0\le V<R_{ijk}$, the cyclic symmetrization of the corresponding literal constituent $\varphi_{ijk}$ of $CW_6^{\otimes4}$ has tau-value at least $V$.
--
--   This strict-lower-base form is the source-faithful encoding of the five limiting exponential-rate bounds in Davie--Stothers Lemma 5.1. The cyclic symmetrization represents the cube in the platform's normalization $\rho=3\tau$. The strict inequality is essential: the platform predicate requires a constant-relative finite witness, whereas the paper's pruning argument may lose a subexponential factor and therefore need not attain the limiting base itself.
-- source:
--   Davie and Stothers (2013), Lemma 5.1(i)-(v), printed pp. 363-366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; Stothers thesis (2010), Chapter 4.3, Lemmas 21-25.

import Definitions.Def_mme_stothers_fourth_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_lemma51_recursive_values
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    (∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 5 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 1 6)) tau V) ∧
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
