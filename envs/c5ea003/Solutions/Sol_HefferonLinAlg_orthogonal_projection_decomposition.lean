-- Prove2me | solution 1 for HefferonLinAlg.orthogonal_projection_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T15:43:19.457689+00:00
-- url     : https://prove2.me/submissions/aa809652-5c47-4e21-9457-1d7c884ef816

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

theorem solution
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (S : Submodule ℝ V) :
    IsCompl S Sᗮ := by
  exact Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
