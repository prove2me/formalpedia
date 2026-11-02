-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_to_edge_maximal__p2m_9aae8c1a_0088_4039_a6d9_b99fa0bd700a_a1
-- name    : WilliamsonShmoys.planar_extension_to_edge_maximal__p2m_9aae8c1a_0088_4039_a6d9_b99fa0bd700a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:08:28.334186+00:00
-- url     : https://prove2.me/theorems/629021cc-ee60-4d9a-a83c-dbd077e630a9
-- title:
--   Finite maximal planar extension
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph on the same vertices that has no strictly larger drawable supergraph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_to_edge_maximal__p2m_9aae8c1a_0088_4039_a6d9_b99fa0bd700a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ K : SimpleGraph V,
          N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by sorry
