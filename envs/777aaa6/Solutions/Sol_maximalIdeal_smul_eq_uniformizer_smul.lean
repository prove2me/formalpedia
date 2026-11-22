-- Prove2me | solution 1 for maximalIdeal_smul_eq_uniformizer_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:44:37.762007+00:00
-- url     : https://prove2.me/submissions/76b311e6-6141-4ca0-a857-51b7d5fa75c1

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings

set_option autoImplicit false
variable {K : Type*} [Field K] (R : Subring K)
variable {R}
open Pointwise
theorem _root_.solution [IsDiscreteValuationRing R] {ι : Type*} [Fintype ι]
    (M : Submodule R (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalRing.maximalIdeal R • M = ϖ • M := by
  rw [hϖ.maximalIdeal_eq]
  exact Submodule.ideal_span_singleton_smul ϖ M
