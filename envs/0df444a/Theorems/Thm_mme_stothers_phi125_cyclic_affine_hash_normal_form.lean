-- Prove2me | Theorems.Thm_mme_stothers_phi125_cyclic_affine_hash_normal_form
-- name    : mme_stothers_phi125_cyclic_affine_hash_normal_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:27:56.681693+00:00
-- url     : https://prove2.me/theorems/312702ae-0498-4fa6-92cd-65eec42dd741
-- title:
--   Linear normal form of the cyclic phi_125 affine hash
-- statement:
--   For each cyclic vertex i, the φ₁₂₅ affine hash is the sum of a common shift, the mode offset c_iδ with (c₀,c₁,c₂)=(0,12,6), and a linear form whose coefficient word is the cyclic mode code: $$H_i(e)=s+c_i\delta+\sum_{r,j}C_i(e)_{r,j}w_{r,j}.$$ This is the normal form used in both the exact edge-retention count and the pair-collision bound.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), affine type-2 hash in Lemma 3.3; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi125_cyclic_hash_data

open BigOperators
open MME.StothersFourth.Phi125

set_option autoImplicit false

theorem mme_stothers_phi125_cyclic_affine_hash_normal_form
    {p N alpha beta gamma : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p) (i : Fin 3)
    (e : CyclicExactEdge N alpha beta gamma) :
    cyclicAffineHash p N alpha beta gamma w shift offset i e =
      shift + (![0, 12 * offset, 6 * offset] : Fin 3 → ZMod p) i +
        ∑ r : Fin 3, ∑ j : Fin (2 * N),
          cyclicHashModeCode p N i (cyclicModeWord e i) r j * w r j := by
  sorry
