-- Prove2me | Theorems.Thm_mme_stothers_phi233_pattern_injective
-- name    : mme_stothers_phi233_pattern_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:40:27.436542+00:00
-- url     : https://prove2.me/theorems/6af4cb1c-6491-40d5-9c14-17003f4467e6
-- title:
--   The ten phi_233 joint patterns are distinct
-- statement:
--   The ten ordered grade triples used in the $\varphi_{233}$ profile,
--
--   $$
--   013,022,031,103,112,121,130,202,211,220,
--   $$
--
--   are pairwise distinct. Consequently, the joint type label of a coordinate is uniquely determined by its three-mode grade pattern. This finite identification is used to transfer prescribed label-fibre cardinalities to exact joint-profile cardinalities.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v), p. 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data

open MME

set_option autoImplicit false

theorem mme_stothers_phi233_pattern_injective :
    Function.Injective MME.StothersFourth.Phi233.pattern := by
  sorry
