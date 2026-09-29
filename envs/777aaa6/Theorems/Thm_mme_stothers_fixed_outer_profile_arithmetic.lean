-- Prove2me | Theorems.Thm_mme_stothers_fixed_outer_profile_arithmetic
-- name    : mme_stothers_fixed_outer_profile_arithmetic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T18:47:30.515451+00:00
-- url     : https://prove2.me/theorems/6fa12584-414c-4892-af38-0ac3b4b16bcd
-- title:
--   Exact arithmetic certificate for the fixed Davie–Stothers outer profile
-- statement:
--   For the exact ten-class distribution used in the fixed fourth-power specialization, all class frequencies are positive and normalized with the Table-1 multiplicities. The finite orbit table has exactly the marginal multiplicities prescribed by Equation (5.2), the resulting nine marginal counts sum to three times the profile scale, and the normalized rational vector satisfies both stationarity equations defining the set N.
--
--   This is a machine-checkable exact replacement for the rounded decimal data used in the numerical discussion. It certifies the finite arithmetic needed before invoking the outer hashing argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved bound for complexity of matrix multiplication, Proceedings of the Royal Society of Edinburgh A 143 (2013), Section 5, Table 1, Equation (5.2), Lemma 5.2 and Theorem 5.3, pp. 366–368; exact rational stationary specialization independently certified from those equations. https://doi.org/10.1017/S0308210511001648

import Definitions.Def_mme_stothers_fixed_outer_profile

open MME BigOperators
open MME.StothersFourth

set_option autoImplicit false

theorem mme_stothers_fixed_outer_profile_arithmetic :
    (∀ i : Fin 10, 0 < fixedProfileBaseCount i) ∧
    (∑ i : Fin 10,
        classMultiplicity i * fixedProfileBaseCount i = fixedProfileScale) ∧
    (∀ r : Fin 10, ∀ s : Fin 3, ∀ j : Fin 9,
      ((fixedClassOrbit r).filter (fun σ ↦ σ s = j)).card =
        fixedClassMarginalMultiplicity r j) ∧
    (∀ j : Fin 9,
      fixedMarginalBaseCount j =
        ∑ r : Fin 10,
          fixedClassMarginalMultiplicity r j * fixedProfileBaseCount r) ∧
    (∑ j : Fin 9, fixedMarginalBaseCount j = 3 * fixedProfileScale) ∧
    InN fixedProfileB := by sorry
