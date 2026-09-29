-- Prove2me | Theorems.Thm_mme_CW_2376_exact_profile_address_supported
-- name    : mme_CW_2376_exact_profile_address_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:16:53.313525+00:00
-- url     : https://prove2.me/theorems/8995fe86-1f60-450e-bf3e-ef1c86722e45
-- title:
--   Exact CW 2.376 profile addresses satisfy five-grade support
-- statement:
--   Every exact-profile address used in the Coppersmith--Winograd 2.376 extraction is supported coordinatewise by the five-grading of the squared tensor. Thus, at every tensor-power coordinate $r$, its three grades satisfy
--
--   $$I_r+J_r+K_r=4.$$
--
--   Indeed, the exact profile assigns positive multiplicity only to the fifteen supported grade triples in equation (13), and assigns multiplicity zero to every other triple. This lemma packages that support consequence for use in the finite hashing and incidence arguments.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), the fifteen supported square grades in equation (11) and exact profile (13), journal pp. 265--268; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_profile_induced_family

open MME

theorem mme_CW_2376_exact_profile_address_supported
    (m : ℕ) (a : CW2376ExactProfileAddress m) :
    CW2376CoordinatewiseSupported a.1 := by
  sorry
