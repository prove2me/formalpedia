-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_edge_maximal_supergraph_same_vertex
-- name    : WilliamsonShmoys.exists_drawable_edge_maximal_supergraph_same_vertex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:50:39.134226+00:00
-- url     : https://prove2.me/theorems/203622c3-a648-410c-9457-113f9f83522b
-- title:
--   Edge-maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices with no strictly larger drawable supergraph. This removes the finite optimization step from the parent: maximize the edge count among drawable supergraphs, then use inclusion and maximality to obtain the required extension. It needs no lower bound on the number of vertices. An independent proof route is to use finiteness of the set of simple graphs on V and choose a maximum-edge member among those containing L and admitting a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_drawable_edge_maximal_supergraph_same_vertex
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
