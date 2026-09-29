-- Prove2me | Theorems.Thm_mme_stothers_fixed_exact_outer_address_regular
-- name    : mme_stothers_fixed_exact_outer_address_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T18:47:40.152257+00:00
-- url     : https://prove2.me/theorems/431df346-f453-443a-be64-df31d8db48d0
-- title:
--   Exact Table-1 profiles have the required Equation-(5.2) marginals
-- statement:
--   At every integral repetition scale m, an outer address having the prescribed exact multiplicity for every permutation of the ten Table-1 classes is automatically coordinatewise supported: its three grades sum to 8 in each position. Moreover, each of its three mode words has exactly the nine-grade marginal obtained from Equation (5.2).
--
--   Thus an exact-profile target edge canonically belongs to the marginal-supported ambient hypergraph used by the type-1 Salem–Spencer extraction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved bound for complexity of matrix multiplication, Proceedings of the Royal Society of Edinburgh A 143 (2013), Section 3, Lemma 3.3, and Section 5, Table 1 and Equation (5.2), pp. 362–368. https://doi.org/10.1017/S0308210511001648

import Definitions.Def_mme_stothers_fixed_outer_profile

open MME BigOperators
open MME.StothersFourth

set_option autoImplicit false

theorem mme_stothers_fixed_exact_outer_address_regular
    (m : ℕ) (a : FixedExactOuterAddress m) :
    FixedCoordinatewiseSupported a.1 ∧ FixedMarginallyRegular a.1 := by sorry
