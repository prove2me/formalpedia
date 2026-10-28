-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_on
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph_on
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:30:53.422629+00:00
-- url     : https://prove2.me/theorems/d51f9707-d3e4-46ba-93e5-2fa0f68034fc
-- title:
--   An edge-maximal drawable supergraph exists
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph that has no strictly larger drawable supergraph on the same vertex type. The finite family of simple graphs makes edge-count maximization a direct proof route.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph_on
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ Q : SimpleGraph V,
        N ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q = N := by
  sorry
