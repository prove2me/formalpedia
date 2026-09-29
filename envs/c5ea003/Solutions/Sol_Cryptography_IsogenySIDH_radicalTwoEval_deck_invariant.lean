-- Prove2me | solution 1 for Cryptography.IsogenySIDH.radicalTwoEval_deck_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T12:39:38.968746+00:00
-- url     : https://prove2.me/submissions/760f094d-bc52-4158-ba06-299c073fa743

import Mathlib
import Definitions.Def_Cryptography_AbstractAlgebra_IsogenyFoundations
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomery
open Cryptography.IsogenySIDH in
theorem solution {K : Type*} [Field K] {x y : K} (hx : x ≠ 0) :
    radicalTwoEval (x⁻¹, -(y * x⁻¹ ^ 2)) = radicalTwoEval (x, y) := by
  unfold radicalTwoEval
  refine Prod.ext ?_ ?_
  · simp only [inv_inv]
    ring
  · simp only [inv_inv]
    field_simp
    ring
