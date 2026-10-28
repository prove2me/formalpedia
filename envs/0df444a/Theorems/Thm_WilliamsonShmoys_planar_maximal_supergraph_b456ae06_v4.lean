-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_b456ae06_v4
-- name    : WilliamsonShmoys.planar_maximal_supergraph_b456ae06_v4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:11:21.097379+00:00
-- url     : https://prove2.me/theorems/f408a743-f18c-4e2c-b096-7e734a346f5b
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable finite simple graph on at least three vertices has an inclusion-maximal drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_supergraph_b456ae06_v4 {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
