-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:01:20.88456+00:00
-- url     : https://prove2.me/theorems/4dc84fc8-9837-496e-bb19-eb0d0139a4ff
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   A drawable finite simple graph has a drawable supergraph that contains all its edges and admits no proper drawable edge extension on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hdraw : HasPlanarDrawingOn L) :
    letI : forall G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    exists M : SimpleGraph V,
      L.edgeFinset ⊆ M.edgeFinset /\
      HasPlanarDrawingOn M /\
      forall N : SimpleGraph V,
        (forall u v, M.Adj u v -> N.Adj u v) ->
        HasPlanarDrawingOn N ->
        forall u v, N.Adj u v -> M.Adj u v := by
  sorry
