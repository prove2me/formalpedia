-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_on_for_arcs
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_on_for_arcs
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:10:25.69203+00:00
-- url     : https://prove2.me/theorems/54a8e8ff-448e-4982-808f-e6f7deb9c201
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every graph with the supplied drawing on a finite vertex type is contained in a drawable supergraph that has no strictly larger drawable supergraph on the same vertex type. The argument can maximize the edge count among the finite set of drawable supergraphs containing the original graph. This removes the augmentation step from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_on_for_arcs
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V,
        N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by sorry
