-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension
-- name    : WilliamsonShmoys.planar_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:00:57.551924+00:00
-- url     : https://prove2.me/theorems/2e5a7384-2edb-4303-982e-6d301b4c99c8
-- title:
--   Extend a finite planar drawing to a maximal planar supergraph
-- statement:
--   Every finite graph on at least three vertices with the supplied planar drawing has a supergraph on the same vertex type that is maximal among planar supergraphs and has at least as many edges. The same-vertex requirement covers disconnected graphs without discarding isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H) := by sorry
