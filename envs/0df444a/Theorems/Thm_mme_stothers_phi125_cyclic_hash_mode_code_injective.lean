-- Prove2me | Theorems.Thm_mme_stothers_phi125_cyclic_hash_mode_code_injective
-- name    : mme_stothers_phi125_cyclic_hash_mode_code_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:23:20.795762+00:00
-- url     : https://prove2.me/theorems/c4e08c2a-84c6-4b9a-b08d-537479cf6f53
-- title:
--   Injectivity of the cyclic phi_125 hash mode code
-- statement:
--   For a prime modulus p≥5 and any cyclic vertex i, the coefficient-word encoding of a length-2N cyclic φ₁₂₅ mode word is injective. This guarantees that two distinct cyclic mode words differ in at least one nonzero hash coefficient, which is the pivot needed for the affine pair-collision bound.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), type-2 affine hash in Lemma 3.3; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi125_cyclic_hash_data

open MME.StothersFourth.Phi125

set_option autoImplicit false

theorem mme_stothers_phi125_cyclic_hash_mode_code_injective
    {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (i : Fin 3) :
    Function.Injective (cyclicHashModeCode p N i) := by
  sorry
