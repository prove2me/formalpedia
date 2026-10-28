-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_augmentation_78919b52_de37_4426_ade1_0aaa5522d1e4
-- name    : WilliamsonShmoys.planar_supergraph_augmentation_78919b52_de37_4426_ade1_0aaa5522d1e4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:15:48.105692+00:00
-- url     : https://prove2.me/theorems/d1924f9c-7f54-4799-87f6-b51d2e21e689
-- title:
--   Planar supergraph augmentation to edge maximality
-- statement:
--   A graph with a crossing-free drawing on at least three vertices has a drawable supergraph on the same vertex set that is maximal under edge inclusion. This removes the finite augmentation step from the parent. Independently, the finite family of graphs on V allows choosing a drawable supergraph with a maximal edge set; any strictly larger drawable supergraph would contradict that choice. The drawing and the bound of at least three vertices are retained.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_augmentation_78919b52_de37_4426_ade1_0aaa5522d1e4
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
