-- Prove2me | Theorems.Thm_mme_stothers_phi125_cyclic_affine_hash_AP
-- name    : mme_stothers_phi125_cyclic_affine_hash_AP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:21:00.931609+00:00
-- url     : https://prove2.me/theorems/e129427d-dfb3-4608-85de-36474218c538
-- title:
--   Arithmetic-progression identity for the cyclic phi_125 hash
-- statement:
--   For three cyclic exact φ₁₂₅ edges whose modewise mixture is coordinatewise supported, the source-faithful affine hashes satisfy the arithmetic-progression relation $$H_0(x)+H_1(y)=2H_2(z).$$ The identity follows from the local five-grade equation x+y+z=4 and is the algebraic input through which a three-AP-free set forces a retained supported triple to be diagonal.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), type-2 hash in Lemma 3.3 and its φ₁₂₅ specialization in Lemma 5.1(ii); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi125_cyclic_hash_data

open MME.StothersFourth.Phi125

set_option autoImplicit false

theorem mme_stothers_phi125_cyclic_affine_hash_AP
    {p N alpha beta gamma : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p)
    (x y z : CyclicExactEdge N alpha beta gamma)
    (hsupp : CyclicCoordinatewiseSupported x y z) :
    cyclicAffineHash p N alpha beta gamma w shift offset 0 x +
        cyclicAffineHash p N alpha beta gamma w shift offset 1 y =
      2 * cyclicAffineHash p N alpha beta gamma w shift offset 2 z := by
  sorry
