-- Prove2me | solution 1 for HefferonLinAlg.rank_plus_nullity
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T15:43:19.150654+00:00
-- url     : https://prove2.me/submissions/ed7498c8-529c-456e-bc10-4c933c612cf0

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

theorem solution
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.ker f) =
      Module.finrank K V := by
  exact f.finrank_range_add_finrank_ker
