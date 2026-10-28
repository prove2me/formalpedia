-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal
-- name    : WilliamsonShmoys.exists_planar_supergraph_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:22:40.018425+00:00
-- url     : https://prove2.me/theorems/019def15-4d01-4175-9d83-3461bf6164ab
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices with no strict drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun K : SimpleGraph V =>
      And (L <= K) (And (WilliamsonShmoys.HasPlanarDrawingOn K)
        (forall K' : SimpleGraph V, K <= K' ->
          WilliamsonShmoys.HasPlanarDrawingOn K' -> K' = K)) := by
  sorry
