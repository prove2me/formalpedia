-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_for_completion
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_for_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:02:27.706179+00:00
-- url     : https://prove2.me/theorems/700fcf5a-84ac-4dbc-af35-289fb336b02d
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal among drawable supergraphs on the same vertices. The proof route is to maximize edge-set cardinality over the finite, nonempty collection of drawable supergraphs containing the original graph; any drawable supergraph of a maximizer must have the same edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_supergraph_for_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by sorry
