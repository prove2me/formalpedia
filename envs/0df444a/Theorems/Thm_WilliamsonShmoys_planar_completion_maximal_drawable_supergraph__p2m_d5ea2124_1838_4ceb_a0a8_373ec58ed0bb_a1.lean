-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_maximal_drawable_supergraph__p2m_d5ea2124_1838_4ceb_a0a8_373ec58ed0bb_a1
-- name    : WilliamsonShmoys.planar_completion_maximal_drawable_supergraph__p2m_d5ea2124_1838_4ceb_a0a8_373ec58ed0bb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:28:28.181628+00:00
-- url     : https://prove2.me/theorems/1d33b6d7-3a1e-4c95-9772-1df7e0d4ddf9
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on that same vertex type that is maximal under edge inclusion among drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_maximal_drawable_supergraph__p2m_d5ea2124_1838_4ceb_a0a8_373ec58ed0bb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      And (Set.Subset H.edgeSet K.edgeSet)
        (And (HasPlanarDrawingOn K)
          (forall L : SimpleGraph V,
            Set.Subset K.edgeSet L.edgeSet ->
            HasPlanarDrawingOn L ->
            Set.Subset L.edgeSet K.edgeSet)) := by sorry
