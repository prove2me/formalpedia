-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_e61f28a9_retry3
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_e61f28a9_retry3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:57:30.952702+00:00
-- url     : https://prove2.me/theorems/1aa3c342-7e83-4d12-b693-d5b093c39073
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs under graph inclusion. The finite proof chooses one with maximum edge-set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_e61f28a9_retry3
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hDraw : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V, T ≤ U ∧ HasPlanarDrawingOn U ∧
      ∀ W : SimpleGraph V, U ≤ W → HasPlanarDrawingOn W → W = U := by sorry
