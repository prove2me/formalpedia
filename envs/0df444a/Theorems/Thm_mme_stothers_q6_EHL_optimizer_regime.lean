-- Prove2me | Theorems.Thm_mme_stothers_q6_EHL_optimizer_regime
-- name    : mme_stothers_q6_EHL_optimizer_regime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:07:21.706795+00:00
-- url     : https://prove2.me/theorems/d0918f00-aa99-4611-86b0-5587fa9584d2
-- title:
--   The q=6 Davie--Stothers E-H-L optimizer regime
-- statement:
--   For q=6 and every exponent parameter rho=3 tau in [2,3], the Davie--Stothers quantities E=(12)^rho, H=(38)^rho, and L=4(6)^rho((6)^rho+2) satisfy 16 ≤ E < H < L < 4H. In addition, they satisfy the two exact cross-multiplied inequalities needed to make the phi_224 optimizer profile feasible: (2+E)L ≤ 2H(E+H) and 2EH ≤ L(2+E+H).
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Equation (5.1) and Lemma 5.1(iv), pp. 364--365, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_stothers_fourth_data

open MME

set_option autoImplicit false

theorem mme_stothers_q6_EHL_optimizer_regime
    (tau : ℝ) (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    16 ≤ MME.StothersFourth.E 6 tau ∧
    MME.StothersFourth.E 6 tau < MME.StothersFourth.H 6 tau ∧
    MME.StothersFourth.H 6 tau < MME.StothersFourth.L 6 tau ∧
    MME.StothersFourth.L 6 tau < 4 * MME.StothersFourth.H 6 tau ∧
    (2 + MME.StothersFourth.E 6 tau) * MME.StothersFourth.L 6 tau ≤
      2 * MME.StothersFourth.H 6 tau *
        (MME.StothersFourth.E 6 tau + MME.StothersFourth.H 6 tau) ∧
    2 * MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau ≤
      MME.StothersFourth.L 6 tau *
        (2 + MME.StothersFourth.E 6 tau + MME.StothersFourth.H 6 tau) := by
  sorry
