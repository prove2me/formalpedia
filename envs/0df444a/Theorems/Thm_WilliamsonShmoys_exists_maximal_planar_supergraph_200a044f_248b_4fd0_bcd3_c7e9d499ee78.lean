-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_200a044f_248b_4fd0_bcd3_c7e9d499ee78
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_200a044f_248b_4fd0_bcd3_c7e9d499ee78
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:40:11.325987+00:00
-- url     : https://prove2.me/theorems/5b956768-6b76-41c7-bfd2-8a4d7962635d
-- title:
--   A finite maximal drawable supergraph exists
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on that same type. Choose a maximal edge set among the finite family of drawable supergraphs containing the input; this does not require connectedness or a lower bound on the vertex count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_200a044f_248b_4fd0_bcd3_c7e9d499ee78
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V,
      L ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V,
        T ≤ U →
        WilliamsonShmoys.HasPlanarDrawingOn U →
        U = T := by
  sorry
