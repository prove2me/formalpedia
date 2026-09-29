-- Prove2me | solution 1 for HefferonLinAlg.dimension_characterizes_isomorphism
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T15:43:18.846223+00:00
-- url     : https://prove2.me/submissions/4d9fd516-2de1-4d18-ac61-23221ab41fd7

import Mathlib.LinearAlgebra.FiniteDimensional.Defs

theorem solution
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] :
    Nonempty (V ≃ₗ[K] W) ↔ Module.finrank K V = Module.finrank K W := by
  exact FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq
