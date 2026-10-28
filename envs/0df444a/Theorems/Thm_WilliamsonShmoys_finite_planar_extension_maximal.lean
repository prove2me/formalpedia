-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_extension_maximal
-- name    : WilliamsonShmoys.finite_planar_extension_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:38:11.882599+00:00
-- url     : https://prove2.me/theorems/2ed85218-e942-4a3b-a6ea-b4201960be52
-- title:
--   Maximal planar extension on a finite vertex type
-- statement:
--   A planar graph on a finite vertex type has a planar supergraph on that same type that is maximal among planar supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_planar_extension_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    exists K : SimpleGraph V,
      G <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      forall H : SimpleGraph V,
        K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K := by sorry
