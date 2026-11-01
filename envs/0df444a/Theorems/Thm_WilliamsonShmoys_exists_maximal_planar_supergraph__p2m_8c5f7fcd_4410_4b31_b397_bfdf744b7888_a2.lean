-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:22:47.727199+00:00
-- url     : https://prove2.me/theorems/8483dba4-46b0-4557-8588-2cfeb83216a6
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on that same type that is maximal under graph inclusion. The finite family of drawable supergraphs containing the input graph provides an independent proof route; the parent uses this result to obtain a graph to which the maximal edge-count result applies.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V => H <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      forall K' : SimpleGraph V, K <= K' -> WilliamsonShmoys.HasPlanarDrawingOn K' -> K' = K := by sorry
