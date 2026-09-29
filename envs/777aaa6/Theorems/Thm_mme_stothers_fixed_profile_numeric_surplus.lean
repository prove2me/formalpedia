-- Prove2me | Theorems.Thm_mme_stothers_fixed_profile_numeric_surplus
-- name    : mme_stothers_fixed_profile_numeric_surplus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:00:38.845899+00:00
-- url     : https://prove2.me/theorems/3f495565-6788-4c1b-83c2-2995f844ab41
-- title:
--   Exact Stothers q = 6 fixed-profile scalar surplus
-- statement:
--   Set
--   $$
--   \tau_0=\frac{23737}{30000}
--   \quad\text{and}\quad
--   b=\frac{1}{97{,}942{,}072}
--   (98,1862,73075,1023050,3626000,98000,2156000,13720000,21560000,38710000).
--   $$
--   For the Davie--Stothers fourth-power rate from Equation (5.3), specialized to $q=6$ and to the same exact profile on both sides, one has
--   $$
--   \left(\frac{640000001}{10000000}\right)^2
--   <
--   \operatorname{globalRate}(6,\tau_0,b,b).
--   $$
--   Thus the fourth-power rate has a strict scalar surplus over the square of $64.0000001$. This exact rational profile is a nearby stationary witness selected to make the numerical specialization formally certifiable; it is not asserted to equal the rounded decimal optimizer printed in Table 2.
--
--   **Formalization Note** The function globalRate is the definition already attached to the mission's formalization of Equation (5.3). The theorem is purely a fixed-profile numerical inequality and makes no tensor-extraction claim.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Equation (5.3), Theorem 5.3, and Table 2, printed pp. 367–368; https://www.maths.ed.ac.uk/~sandy/a11164.pdf; DOI 10.1017/S0308210511001646. The exact rational profile is a formally audited nearby stationary witness, not a claim about the exact unrounded Table 2 optimizer.

import Definitions.Def_mme_stothers_fourth_data

open MME

theorem mme_stothers_fixed_profile_numeric_surplus :
    let tau0 : ℝ := 23737 / 30000
    let numericB : Fin 10 → ℝ :=
      ![(98 : ℝ) / 97942072,
        (1862 : ℝ) / 97942072,
        (73075 : ℝ) / 97942072,
        (1023050 : ℝ) / 97942072,
        (3626000 : ℝ) / 97942072,
        (98000 : ℝ) / 97942072,
        (2156000 : ℝ) / 97942072,
        (13720000 : ℝ) / 97942072,
        (21560000 : ℝ) / 97942072,
        (38710000 : ℝ) / 97942072]
    (640000001 / 10000000 : ℝ) ^ (2 : ℕ) <
      MME.StothersFourth.globalRate 6 tau0 numericB numericB := by
  sorry
