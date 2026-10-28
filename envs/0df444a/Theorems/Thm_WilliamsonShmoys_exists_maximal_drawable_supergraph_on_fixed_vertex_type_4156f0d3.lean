-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_on_fixed_vertex_type_4156f0d3
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_on_fixed_vertex_type_4156f0d3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:54:52.195998+00:00
-- url     : https://prove2.me/theorems/19e1f0c4-ed52-4fec-9c0c-4787de5a4920
-- title:
--   Maximal drawable supergraph on the fixed vertex type
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is inclusion maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_on_fixed_vertex_type_4156f0d3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      Set.Subset G.edgeSet H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, Set.Subset H.edgeSet K.edgeSet →
        HasPlanarDrawingOn K → Set.Subset K.edgeSet H.edgeSet) := by sorry
