-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_connected_extension_b575eb0b_092c_4d6e_a44b_f1a402a11573
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_connected_extension_b575eb0b_092c_4d6e_a44b_f1a402a11573
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:02:49.136058+00:00
-- url     : https://prove2.me/theorems/4b6026a4-6141-4e39-9e16-05bb34634b4a
-- title:
--   A drawable graph has an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on the finite vertex type has a drawable supergraph that has no proper drawable supergraph on that vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_connected_extension_b575eb0b_092c_4d6e_a44b_f1a402a11573
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ M : SimpleGraph V,
      J ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N →
          WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
