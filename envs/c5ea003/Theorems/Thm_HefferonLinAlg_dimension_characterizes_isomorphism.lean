-- Prove2me | Theorems.Thm_HefferonLinAlg_dimension_characterizes_isomorphism
-- name    : HefferonLinAlg.dimension_characterizes_isomorphism
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-05T05:33:28.46127+00:00
-- url     : https://prove2.me/theorems/7d2831ae-109f-4c98-b25e-d8152c9caf42
-- title:
--   Dimension characterizes isomorphism
-- statement:
--   Two finite-dimensional vector spaces $V$ and $W$ over the same field $K$ are isomorphic if and only if they have the same dimension. Finite-dimensional vector spaces are therefore classified up to isomorphism by a single natural number; everything else about such a space is structure carried on top of its dimension.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter Three, Section I.2, Theorem 2.3, p. 194

import Mathlib

open Matrix

namespace HefferonLinAlg

theorem dimension_characterizes_isomorphism
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] :
    Nonempty (V ≃ₗ[K] W) ↔ Module.finrank K V = Module.finrank K W := by
  sorry

end HefferonLinAlg
