-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_e0af0c25_eda4_4a07_86fb_83c9b4328991
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph_e0af0c25_eda4_4a07_86fb_83c9b4328991
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:18:58.520983+00:00
-- url     : https://prove2.me/theorems/a1cf560b-49c8-42ff-bc62-4e696649a626
-- title:
--   Maximal drawable supergraph exists
-- statement:
--   Every drawable simple graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under graph inclusion among drawable graphs. This reuses the exact drawing predicate and finite vertex assumptions. A proof can maximize the edge count over the finite collection of drawable supergraphs containing M; a proper supergraph has strictly more edges. The child removes the existence and maximality step from the parent. It does not use a vertex-count lower bound, so it also covers smaller vertex sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph_e0af0c25_eda4_4a07_86fb_83c9b4328991
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by sorry
