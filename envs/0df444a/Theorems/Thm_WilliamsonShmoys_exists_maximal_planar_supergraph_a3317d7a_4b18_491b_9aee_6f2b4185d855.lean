-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_a3317d7a_4b18_491b_9aee_6f2b4185d855
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_a3317d7a_4b18_491b_9aee_6f2b4185d855
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:16:55.510518+00:00
-- url     : https://prove2.me/theorems/462db292-231b-4457-99c7-e897cbf82d7a
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   A drawable simple graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_a3317d7a_4b18_491b_9aee_6f2b4185d855
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V,
      LE.le Y Z ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      ∀ W : SimpleGraph V,
        LE.le Z W →
        WilliamsonShmoys.HasPlanarDrawingOn W →
        W = Z := by sorry
