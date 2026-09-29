-- Prove2me | Theorems.Thm_mme_recursive_yz_boundary_exact_code_card
-- name    : mme_recursive_yz_boundary_exact_code_card
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T12:49:54.6428+00:00
-- url     : https://prove2.me/theorems/3ccbc789-269a-4b08-9618-81b8371ef901
-- title:
--   Exact dimension of a CW5 boundary profile
-- statement:
--   For every integer complete-word profile with L positions, the number of literal CW5 boundary words realizing that profile is exactly (L! divided by the product of all profile factorials) times 5 to the total number of grade-one positions. Every arrangement of complete fine words and every choice of the five middle CW coordinates is counted; no representative-word restriction is imposed. The formula includes the empty tensor power.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6, Theorem 6.2: exact integer-profile count underlying its entropy dimension estimate.

import Definitions.Def_mme_recursive_yz_boundary_data
open MME MME.CompleteSplit MME.RecursiveYZ.Boundary
set_option autoImplicit false

theorem mme_recursive_yz_boundary_exact_code_card {ell L : ℕ} (B : MME.RecursiveYZ.Boundary.Profile ell L) :
    Fintype.card (Code ell L B.count) = B.dim := by sorry
