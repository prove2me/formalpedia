-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_8895f479_77a0_4c1e_903f_b3af7ab1e8bd_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_8895f479_77a0_4c1e_903f_b3af7ab1e8bd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T12:46:13.819784+00:00
-- url     : https://prove2.me/theorems/90cbbd5c-48b8-4938-99ca-cd8db48989ee
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal among drawable supergraphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_8895f479_77a0_4c1e_903f_b3af7ab1e8bd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      Set.Subset G.edgeSet K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        Set.Subset K.edgeSet L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        K.edgeSet = L.edgeSet := by sorry
