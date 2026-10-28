-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_v2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:01:59.456693+00:00
-- url     : https://prove2.me/theorems/67f6d27e-0df6-44b7-873f-d3d048e638dd
-- title:
--   Every drawable finite graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertex set that is maximal among drawable supergraphs. This removes the augmentation and maximality selection from the parent. A concrete proof route is to maximize edge count over the finite nonempty family of drawable supergraphs containing M; equal edge counts under inclusion imply equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M ≤ N ∧
      ∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K → N ≤ K → K = N := by sorry
