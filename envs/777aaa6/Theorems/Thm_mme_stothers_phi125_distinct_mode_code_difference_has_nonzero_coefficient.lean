-- Prove2me | Theorems.Thm_mme_stothers_phi125_distinct_mode_code_difference_has_nonzero_coefficient
-- name    : mme_stothers_phi125_distinct_mode_code_difference_has_nonzero_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:29:46.309285+00:00
-- url     : https://prove2.me/theorems/9575edad-c9b8-4049-a0c8-cb1bb845c779
-- title:
--   A distinct phi_125 mode gives a nonzero hash coefficient
-- statement:
--   For a prime modulus p≥5, two distinct cyclic φ₁₂₅ mode words have coefficient codes differing at some component r and position j. Thus their coefficient difference has a nonzero pivot, enabling the standard one-linear-equation bound for joint hash retention.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), affine type-2 collision estimate in Lemma 3.3; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi125_cyclic_hash_data
import Theorems.Thm_mme_stothers_phi125_cyclic_hash_mode_code_injective

open MME.StothersFourth.Phi125

set_option autoImplicit false

theorem mme_stothers_phi125_distinct_mode_code_difference_has_nonzero_coefficient
    {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (i : Fin 3) (u v : CyclicModeWord N) (huv : u ≠ v) :
    ∃ r : Fin 3, ∃ j : Fin (2 * N),
      cyclicHashModeCode p N i u r j -
        cyclicHashModeCode p N i v r j ≠ 0 := by
  sorry
