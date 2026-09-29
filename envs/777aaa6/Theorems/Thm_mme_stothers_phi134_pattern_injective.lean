-- Prove2me | Theorems.Thm_mme_stothers_phi134_pattern_injective
-- name    : mme_stothers_phi134_pattern_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:21:59.065871+00:00
-- url     : https://prove2.me/theorems/d0eedd2e-cba6-40da-95fd-c28ca7d960d7
-- title:
--   The eight phi_134 fine-component patterns are injectively labelled
-- statement:
--   The eight three-mode fine types $$004,013,022,031,103,112,121,130$$ occurring in $\Phi_{1,3,4}$ are pairwise distinct. Hence their finite label map into three-mode square grades is injective. This supplies uniqueness for the coordinate label used in exact-profile factorization.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(iii), p. 365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_profile_data

open MME
open MME.StothersFourth.Phi134

set_option autoImplicit false

theorem mme_stothers_phi134_pattern_injective :
    Function.Injective MME.StothersFourth.Phi134.pattern := by
  sorry
