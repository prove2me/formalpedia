-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_for_tight_completion
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_for_tight_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:12:56.994803+00:00
-- url     : https://prove2.me/theorems/2996226b-ee8d-4a5c-87cc-c24217a15ea6
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph maximal among drawable supergraphs on the same vertex type. The proof route is to choose a supergraph with maximum edge-set cardinality from the finite collection of drawable supergraphs containing N; any drawable extension then has the same edge set and equals the chosen graph. This discharges the finite maximality selection in the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_for_tight_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    exists K : SimpleGraph V,
      N <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      (forall L : SimpleGraph V,
        K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) := by sorry
